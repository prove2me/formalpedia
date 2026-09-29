-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_orthogonal_isIrreducibleCuspSubrep_sum_eq_of_apply_eq_smul
-- name    : AutomorphicForm.CuspidalSpectrum.exists_orthogonal_isIrreducibleCuspSubrep_sum_eq_of_apply_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/b685940a-9c5f-5c06-adab-4bf39fa7ceb3
-- title:
--   Eigenvector of a compact cuspidal smoothing operator decomposes discretely
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta\in\mathbb{R}$ and let $\Phi_0\subseteq \mathrm{GL}_2(\mathbb{A}_F)$ satisfy `IsSlabFundamentalDomain`, i.e. $0<\alpha<\beta$, every $g\in\Phi_0$ has idele norm of $\det g$ in $[\alpha,\beta]$, and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_2(F)$ acting on the determinant-norm slab, for the adelic Haar measure restricted to that slab. Let $\sigma\in\mathbb{R}$ and let $\xi$ be a homomorphism from the full subgroup of ideles $\mathbb{A}_F^\times$ to $\mathbb{C}^\times$ with $\|\xi(z)\|=\|z\|^{\sigma}$ for all $z$. Let $f:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be factorizable, that is $f(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ for an archimedean and a finite test factor, and archimedean bi-finite for a family `tys` assigning to each infinite place finitely many archimedean types: $g\mapsto f(g^{-1})$ lies in `archCutSubmodule` and $f$ in `archDualCutSubmodule`. Let $T_c$ be a continuous $\mathbb{C}$-linear endomorphism of the cuspidal sub-carrier $\mathcal H_{\mathrm{cusp}}$ at $(\Phi_0,\sigma,\xi)$ (the closure, inside the weighted $L^2$-space, of the image of the cuspidal automorphic members) which lifts $\varphi\mapsto\mathrm{rightConv}\,\varphi\,f$, $g\mapsto\int \varphi(gx)f(x)\,dx$, in the sense of `IsCuspLift`, and assume $T_c$ is a compact operator. Let $\lambda\neq 0$ and $v\in\mathcal H_{\mathrm{cusp}}$ with $T_cv=\lambda v$. Then there exist $n\in\mathbb{N}$, submodules $M_0,\dots,M_{n-1}\le\mathcal H_{\mathrm{cusp}}$ and vectors $v_0,\dots,v_{n-1}$ such that each $M_i$ satisfies `IsIrreducibleCuspSubrep`, namely `IsClosedCuspSubrep` holds for $M_i$, $M_i\neq 0$, and every submodule satisfying `IsClosedCuspSubrep` contained in $M_i$ is $0$ or $M_i$; the $M_i$ are pairwise orthogonal; $v_i\in M_i$ with $T_cv_i=\lambda v_i$; and $v=\sum_i v_i$.
--
--   This is the discrete decomposition of the cuspidal spectrum in the form needed here: a nonzero eigenvalue eigenvector of a compact bi-finite convolution operator lies in a finite orthogonal sum of irreducible closed cuspidal sub-representations. It feeds the statements about isotypic cuspidal subspaces and cuspidal constituents, in particular the existence of orthonormal systems of cuspidal constituents at level one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_orthogonal_isIrreducibleCuspSubrep_sum_eq_of_apply_eq_smul.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.CuspidalSpectrum.exists_orthogonal_isIrreducibleCuspSubrep_sum_eq_of_apply_eq_smul
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (tys : ArchTypeFamily F)
    (hft : IsArchBiFinite F tys f)
    (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hTc : IsCuspLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) Tc) (hcpt : IsCompactOperator Tc)
    (lam : ℂ) (hlam : lam ≠ 0) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hv : Tc v = lam • v) :
    ∃ (n : ℕ) (M : Fin n → Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (vs : Fin n → ↥(cuspSubcarrier F hΦ₀ σ ξ)),
      (∀ i, IsIrreducibleCuspSubrep F hΦ₀ σ ξ (M i)) ∧
      (Pairwise fun i j => (M i) ⟂ (M j)) ∧
      (∀ i, vs i ∈ M i ∧ Tc (vs i) = lam • vs i) ∧
      v = ∑ i, vs i := by sorry
