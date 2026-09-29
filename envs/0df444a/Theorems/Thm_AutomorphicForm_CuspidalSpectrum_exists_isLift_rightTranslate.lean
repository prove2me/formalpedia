-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightTranslate
-- name    : AutomorphicForm.CuspidalSpectrum.exists_isLift_rightTranslate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/a59c392e-73ef-54ae-aa77-0929d108b259
-- title:
--   Right translation lifts to bounded operators on the weighted L² carrier
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta\in\mathbb R$ and let $\Phi_0\subseteq \mathrm{GL}_2(\mathbb A_F)$ satisfy `IsSlabFundamentalDomain F α β Φ₀`, i.e. $0<\alpha<\beta$, every $g\in\Phi_0$ has $\|\det g\|_{\mathbb A}\in[\alpha,\beta]$ (the idele norm being the module of the multiplication action on the adeles), and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_2(F)$ in $\mathrm{GL}_2(\mathbb A_F)$ acting on the adelic Haar measure restricted to the slab $\{g:\|\det g\|_{\mathbb A}\in[\alpha,\beta]\}$. Let $\sigma\in\mathbb R$, let $\xi$ be a homomorphism from the full subgroup of $\mathbb A_F^\times$ to $\mathbb C^\times$ with $\|\xi(z)\|=\|z\|_{\mathbb A}^{\sigma}$ for all $z$, and let $y\in \mathrm{GL}_2(\mathbb A_F)$. Then on the carrier $L^2$ of the measure `weightedMeasure F Φ₀ σ` (Haar measure restricted to $\Phi_0$, weighted by the density `weight F σ`) there exist continuous $\mathbb C$-linear operators $T,T'$ such that $T$ is a lift of $\varphi\mapsto\varphi(\cdot\,y)$ and $T'$ a lift of $\varphi\mapsto\varphi(\cdot\,y^{-1})$, in the sense that each of these translations preserves the submodule of continuous members of `memberSubmodule F Φ₀ ξ` and the operator agrees with it on the classes of such members, and moreover the adjoint of $T$ equals $\|\det y\|_{\mathbb A}^{\sigma}\cdot T'$ and $\|T\|\le\|\det y\|_{\mathbb A}^{\sigma/2}$.
--
--   This is the translation half of the operator calculus on the cuspidal spectrum: it realises right translation by an adelic matrix as a bounded operator on the weighted $L^2$ space attached to a slab fundamental domain, with the weighted adjoint relation that makes the lift unitary when $\|\det y\|_{\mathbb A}=1$ and a scaled isometry for Hecke representatives. It is invoked by the constructions of commuting lifts of coset sums, of Hecke coset sums and of translations by archimedean row isometries and by compact level groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightTranslate.lean

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

theorem AutomorphicForm.CuspidalSpectrum.exists_isLift_rightTranslate
    (F : Type) [Field F] [NumberField F] (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 F) F))
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ) (y : AdelicGL2 (𝓞 F) F) :
    ∃ T T' : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ,
      IsLift F hΦ₀ σ ξ (rightTranslate F y) T ∧
      IsLift F hΦ₀ σ ξ (rightTranslate F y⁻¹) T' ∧
      ContinuousLinearMap.adjoint T =
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) • T' ∧
      ‖T‖ ≤ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ (σ / 2) := by sorry
