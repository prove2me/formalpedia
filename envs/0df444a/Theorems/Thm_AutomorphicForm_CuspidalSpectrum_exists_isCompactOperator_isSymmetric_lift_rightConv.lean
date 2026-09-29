-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isCompactOperator_isSymmetric_lift_rightConv
-- name    : AutomorphicForm.CuspidalSpectrum.exists_isCompactOperator_isSymmetric_lift_rightConv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/47c7ef3e-ac9f-5e25-9e67-c7f5ad382b13
-- title:
--   Compact symmetric smoothing operator on the cuspidal spectrum
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta\in\mathbb{R}$ and let $\Phi_0\subseteq \mathrm{GL}_2(\mathbb{A}_F)$ satisfy `IsSlabFundamentalDomain F α β Φ₀`: $0<\alpha<\beta$, $\Phi_0$ is contained in the slab $\{g:\lVert\det g\rVert_{\mathbb{A}}\in[\alpha,\beta]\}$, and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_2(F)$ acting on the slab with the restricted adelic Haar measure. Let $\sigma\in\mathbb{R}$ and let $\xi$ be a homomorphism from the full subgroup of $\mathbb{A}_F^{\times}$ to $\mathbb{C}^{\times}$ of modulus $\sigma$, i.e. $\lVert\xi(z)\rVert=\lVert z\rVert_{\mathbb{A}}^{\sigma}$. Let $f:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be a factorizable test function, that is $f(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ for an archimedean and a finite test factor, and assume $f$ is flat-invariant: $\overline{f(y^{-1})}\,\lVert\det y\rVert_{\mathbb{A}}^{-\sigma}=f(y)$ for all $y$. Then there exists a continuous $\mathbb{C}$-linear operator $T_c$ on `cuspSubcarrier F hΦ₀ σ ξ` — the topological closure, inside the carrier space $\mathrm{Carrier}\,F\,\Phi_0\,\sigma$, of the image of the cuspidal members (continuous functions satisfying `IsSmoothCuspAutomorphicFnAt F (fdPins F Φ₀) ξ`) — such that $T_c$ is a compact operator, is symmetric for the inner product ($\langle T_cx,y\rangle=\langle x,T_cy\rangle$), and lifts right convolution by $f$: for every cuspidal member $\varphi$ such that $(\varphi*f)(g)=\int \varphi(gx)f(x)\,dx$ is again a cuspidal member, $T_c$ sends the class of $\varphi$ to the class of $\varphi*f$.
--
--   This is the analytic input making the cuspidal spectrum of $\mathrm{GL}_2$ over a number field discretely decomposable: smoothing by a flat-symmetric test function acts on the cuspidal subspace as a compact self-adjoint operator, so spectral theory applies. It is used by the eigen-capture results for cuspidal constituents, which extract nonzero simultaneous eigenvectors for such convolution operators on isotypic cuspidal subspaces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_isCompactOperator_isSymmetric_lift_rightConv.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalSpectrum.exists_isCompactOperator_isSymmetric_lift_rightConv
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (hflat : flat F σ f = f) :
    ∃ Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      IsCompactOperator Tc ∧ (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)).IsSymmetric ∧
      ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) (hφ' : rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ),
        Tc (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ f, hφ'⟩ := by sorry
