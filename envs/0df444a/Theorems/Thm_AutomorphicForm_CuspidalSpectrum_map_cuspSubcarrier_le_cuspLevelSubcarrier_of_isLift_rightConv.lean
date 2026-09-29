-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_map_cuspSubcarrier_le_cuspLevelSubcarrier_of_isLift_rightConv
-- name    : AutomorphicForm.CuspidalSpectrum.map_cuspSubcarrier_le_cuspLevelSubcarrier_of_isLift_rightConv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/3e23703e-71b2-590e-8e55-469c9448fa96
-- title:
--   Smoothing maps the cuspidal subcarrier into its level-N part
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta$ be reals and $\Phi_0$ a subset of $\mathrm{GL}_2$ of the adeles of $F$ satisfying `IsSlabFundamentalDomain`: $0<\alpha<\beta$, every $g\in\Phi_0$ has idele norm of $\det g$ in $[\alpha,\beta]$, and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_2(F)$ acting on the adelic $\mathrm{GL}_2$ Haar measure restricted to that determinant slab. Let $\sigma\in\mathbb{R}$, let $\xi$ be a homomorphism from the full group of ideles units to $\mathbb{C}^\times$, let $N$ be an ideal of $\mathcal{O}_F$, and let $f$ be a complex function on adelic $\mathrm{GL}_2$ which is a factorizable test function (a product of an archimedean and a finite test factor) and is left invariant under the level group $U(N)=U_1(N)\cap K_f$ attached to $\Phi_0$, i.e. $f(ux)=f(x)$ for all $x$ and all $u\in U(N)$. Let $T$ be a continuous $\mathbb{C}$-linear operator on the carrier $L^2$ space $L^2(\Phi_0,\sigma)$ which lifts right convolution $\varphi\mapsto\varphi*f$, $(\varphi*f)(g)=\int\varphi(gx)f(x)\,dx$: convolution preserves the continuous $\xi$-members, and $T$ sends the class of such a $\varphi$ to the class of $\varphi*f$. Then the image under $T$ of the cuspidal subcarrier (the closed span of classes of cuspidal continuous members) lies in the level-$N$ cuspidal subcarrier (the closed span of classes of cuspidal continuous members $\varphi$ with $\varphi(gu)=\varphi(g)$ for all $g$ and all $u\in U(N)$).
--
--   This is the standard statement that convolution with a test function left invariant under a level group has range in the right $U(N)$-invariants, here in the $L^2$ carrier of the cuspidal spectrum of $\mathrm{GL}_2$ over a number field. It feeds the construction of Hecke coset operators commuting with the projection onto the level-$N$ part, being cited by [`AutomorphicForm.CuspidalSpectrum.exists_commute_lift_heckeCosetSum_of_isLevelSphericalOfType`](thm.html#AutomorphicForm.CuspidalSpectrum.exists_commute_lift_heckeCosetSum_of_isLevelSphericalOfType).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_map_cuspSubcarrier_le_cuspLevelSubcarrier_of_isLift_rightConv.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalSpectrum.map_cuspSubcarrier_le_cuspLevelSubcarrier_of_isLift_rightConv
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (N : Ideal (𝓞 F))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hfU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ (fdPins F Φ₀).U N, f (u * x) = f x)
    (T : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ) (hT : IsLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) T) :
    Submodule.map (T : Carrier F Φ₀ σ →ₗ[ℂ] Carrier F Φ₀ σ) (cuspSubcarrier F hΦ₀ σ ξ) ≤
      cuspLevelSubcarrier F hΦ₀ σ ξ N := by sorry
