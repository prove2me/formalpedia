-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_nhds_forall_norm_toCarrier_rightTranslate_sub_lt
-- name    : AutomorphicForm.CuspidalSpectrum.exists_nhds_forall_norm_toCarrier_rightTranslate_sub_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/90dab80a-4be9-5746-9fe8-70e72878a71f
-- title:
--   Strong continuity of right translation on the weighted L² carrier
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta\in\mathbb{R}$ and let $\Phi_0$ be a subset of $\mathrm{GL}_2(\mathbb{A}_F)$ (the type `AdelicGL2 (𝓞 F) F`) satisfying `IsSlabFundamentalDomain F α β Φ₀`: $0<\alpha<\beta$, every $g\in\Phi_0$ has idele norm of $\det g$ in $[\alpha,\beta]$, and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_2(F)$ under `globalPoints` acting on the adelic Haar measure `adelicGLHaar` restricted to that determinant slab. Let $\sigma\in\mathbb{R}$ and let $\xi$ be a homomorphism from the full subgroup of $\mathbb{A}_F^\times$ to $\mathbb{C}^\times$ of modulus $\sigma$, i.e. $\|\xi(z)\|=\mathrm{ideleNorm}_F(z)^{\sigma}$ for all $z$. Let $x:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ lie in `contMemberSubmodule F Φ₀ ξ`, that is, $x$ is continuous and satisfies the automorphy predicate `IsAutomorphicFnAt F (fdPins F Φ₀) ξ` cutting out `memberSubmodule F Φ₀ ξ`, and let $\varepsilon>0$. Then there is a set $V$ in the neighbourhood filter of the identity of $\mathrm{GL}_2(\mathbb{A}_F)$ such that for every $y\in V$ the translate `rightTranslate F y x` $=\,g\mapsto x(gy)$ again lies in `contMemberSubmodule F Φ₀ ξ`, and the classes of this translate and of $x$ in the carrier $L^2(\mathbb{C},2,$ `weightedMeasure F Φ₀ σ`$)$, formed by the linear map `toCarrier F hΦ₀ σ ξ`, differ in norm by less than $\varepsilon$.
--
--   This is the per-vector strong continuity at the identity of the right regular action of $\mathrm{GL}_2(\mathbb{A}_F)$ on the weighted $L^2$ space of automorphic functions with central character $\xi$ over a slab fundamental domain; the neighbourhood $V$ depends on both $x$ and $\varepsilon$. It is the continuity input for the construction of the associated unitary representation and of its cuspidal subrepresentation, being used in the results that produce a homomorphism into lifts of right translation with prescribed norms and continuity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_nhds_forall_norm_toCarrier_rightTranslate_sub_lt.lean

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

open scoped Topology

theorem AutomorphicForm.CuspidalSpectrum.exists_nhds_forall_norm_toCarrier_rightTranslate_sub_lt
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hx : x ∈ contMemberSubmodule F Φ₀ ξ) (ε : ℝ) (hε : 0 < ε) :
    ∃ V ∈ 𝓝 (1 : AdelicGL2 (𝓞 F) F), ∀ y ∈ V, ∃ hy : rightTranslate F y x ∈ contMemberSubmodule F Φ₀ ξ,
      ‖toCarrier F hΦ₀ σ ξ ⟨rightTranslate F y x, hy.1⟩ - toCarrier F hΦ₀ σ ξ ⟨x, hx.1⟩‖ < ε := by sorry
