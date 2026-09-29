-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isArchBiFinite_flat_isCompactOperator_lift_rightConv_apply_ne_zero
-- name    : AutomorphicForm.CuspidalSpectrum.exists_isArchBiFinite_flat_isCompactOperator_lift_rightConv_apply_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/7a6fb9b4-6747-5c76-8544-7105ce0df401
-- title:
--   Flat bi-finite smoothings separate vectors of the cuspidal sub-carrier
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta\in\mathbb R$ and let $\Phi_0\subseteq \mathrm{GL}_2(\mathbb A_F)$ satisfy `IsSlabFundamentalDomain`, i.e. $0<\alpha<\beta$, $\Phi_0$ is contained in the slab $\{g:\ \|\det g\|\in[\alpha,\beta]\}$ and is a fundamental domain for the image of $\mathrm{GL}_2(F)$ acting on adelic Haar measure restricted to that slab. Let $\sigma\in\mathbb R$ and let $\xi$ be a homomorphism from the full subgroup of $\mathbb A_F^\times$ to $\mathbb C^\times$ with modulus $\sigma$, meaning $\|\xi(z)\|=\|z\|^{\sigma}$ for all $z$. Let $v$ be a non-zero element of `cuspSubcarrier`, the closure in $L^2$ of the weighted measure attached to $(\Phi_0,\sigma)$ of the image of the cuspidal automorphic members of type $\xi$. Then there exist a family $\tau$ of archimedean types (a number $\mathrm{card}(w)$ of representations at each infinite place $w$, together with those representations) and a function $f$ on $\mathrm{GL}_2(\mathbb A_F)$ such that: $f$ factorises as an archimedean test factor at the infinite places times a finite test factor; $f$ is archimedean bi-finite of type $\tau$, i.e. $y\mapsto f(y^{-1})$ lies in the archimedean cut submodule of $\tau$ and $f$ in the dual cut submodule; $f$ is fixed by the $\sigma$-flat involution, $\overline{f(y^{-1})}\,\|\det y\|^{-\sigma}=f(y)$ for all $y$; and there is a continuous $\mathbb C$-linear operator $T$ on the cuspidal sub-carrier which is a compact operator, symmetric as a linear map, lifts right convolution by $f$ (for every cuspidal member $\varphi$ with $g\mapsto\int \varphi(gx)f(x)\,dx$ again a cuspidal member, $T$ sends the class of $\varphi$ to the class of that convolution), and satisfies $Tv\neq 0$.
--
--   This is the separating statement used for the spectral analysis of the cuspidal sub-carrier: the compact symmetric operators obtained by smoothing with flat, factorizable, archimedean bi-finite test functions have no common kernel. It is invoked in producing non-zero $K$-finite vectors in non-trivial closed cuspidal sub-representations and in the construction of orthonormal bases of isotypic cuspidal subspaces at level one and at principal level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_isArchBiFinite_flat_isCompactOperator_lift_rightConv_apply_ne_zero.lean

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

theorem AutomorphicForm.CuspidalSpectrum.exists_isArchBiFinite_flat_isCompactOperator_lift_rightConv_apply_ne_zero
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hv : v ≠ 0) :
    ∃ (tys : ArchTypeFamily F) (f : AdelicGL2 (𝓞 F) F → ℂ),
      IsFactorizableTestFn F f ∧ IsArchBiFinite F tys f ∧ flat F σ f = f ∧
      ∃ Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
        IsCompactOperator Tc ∧ (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)).IsSymmetric ∧
        IsCuspLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) Tc ∧ Tc v ≠ 0 := by sorry
