-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightConv
-- name    : AutomorphicForm.CuspidalSpectrum.exists_isLift_rightConv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/a61b85d0-3388-583f-8716-d59fd8de47fa
-- title:
--   Right convolution lifts to an adjoint pair of operators
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta\in\mathbb{R}$ and let $\Phi_0\subseteq \mathrm{GL}_2(\mathbb{A}_F)$ satisfy `IsSlabFundamentalDomain`, i.e. $0<\alpha<\beta$, every $g\in\Phi_0$ has $\lVert\det g\rVert_{\mathbb{A}}\in[\alpha,\beta]$ (the idele norm being the distributive Haar character of the adele ring), and $\Phi_0$ is a fundamental domain for the action of the image of $\mathrm{GL}_2(F)$ in $\mathrm{GL}_2(\mathbb{A}_F)$ on the slab $\{\,\lVert\det g\rVert_{\mathbb{A}}\in[\alpha,\beta]\,\}$ with respect to the adelic Haar measure `adelicGLHaar` restricted to that slab. Let $\sigma\in\mathbb{R}$ and let $\xi$ be a homomorphism from the full subgroup of the idele units to $\mathbb{C}^\times$ with $\lVert\xi(z)\rVert=\lVert z\rVert_{\mathbb{A}}^{\sigma}$ for all $z$. Let $g:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be continuous with compact support. The assertion is that there exist continuous linear operators $T,T'$ on `Carrier F Φ₀ σ`, the space $L^2$ of the adelic Haar measure restricted to $\Phi_0$ with density `weight F σ`, such that $T$ is a lift of the map $\varphi\mapsto \varphi*g$, where $(\varphi*g)(x)=\int \varphi(xy)g(y)\,dy$ against adelic Haar measure, and $T'$ is a lift of $\varphi\mapsto\varphi*g^{\flat}$ with $g^{\flat}(y)=\overline{g(y^{-1})}\,\lVert\det y\rVert_{\mathbb{A}}^{-\sigma}$; here being a lift (`IsLift`) means that the operation in question carries the continuous elements of the submodule `memberSubmodule F Φ₀ ξ` into themselves and that the operator agrees with it after passage to $L^2$-classes via `toCarrier`. Moreover the Hilbert-space adjoint of $T$ is $T'$.
--
--   This is the adelic smoothing construction of the spectral theory of cusp forms: convolution on the right by a continuous compactly supported test function is realised as a bounded operator on the weighted $L^2$ space attached to a slab fundamental domain, with the convolution by $g^{\flat}$ as its adjoint. It is one of the ingredients used in the admissibility and eigenvector-capture statements for cuspidal constituents of $\mathrm{GL}(2)$ over a number field, such as [`AutomorphicForm.CuspidalSpectrum.exists_commute_lift_cosetSum_of_isLevelSphericalOfType_of_isCompact`](thm.html#AutomorphicForm.CuspidalSpectrum.exists_commute_lift_cosetSum_of_isLevelSphericalOfType_of_isCompact) and the results on level-spherical constituents that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightConv.lean

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

theorem AutomorphicForm.CuspidalSpectrum.exists_isLift_rightConv
    (F : Type) [Field F] [NumberField F] (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 F) F))
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (g : AdelicGL2 (𝓞 F) F → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∃ T T' : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ,
      IsLift F hΦ₀ σ ξ (fun φ => rightConv F φ g) T ∧
      IsLift F hΦ₀ σ ξ (fun φ => rightConv F φ (flat F σ g)) T' ∧
      ContinuousLinearMap.adjoint T = T' := by sorry
