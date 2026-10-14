-- Prove2me | Theorems.Thm_ChanceStateCtrl_AlmostSure_theorem_3_9
-- name    : ChanceStateCtrl.AlmostSure.theorem_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:53.764128+00:00
-- url     : https://prove2.me/theorems/1cb645a6-8b68-43aa-9336-b460681ef0f4
-- title:
--   Theorem 3.9 (Ioffe and Levin), p. 21 — unique decomposition of (L∞_P(Ω, X))* into absolutely continuous and singular parts
-- statement:
--   Let $X$ be a separable Banach space and $(\Omega,\mathcal F,\mathbb P)$ a probability space. Every continuous linear functional $v^*\in(L^\infty_{\mathbb P}(\Omega,X))^*$ has a unique decomposition
--   $$v^*=v^a+v^\circ,$$
--   where $v^a$ is absolutely continuous (of the form $\langle v^a,x\rangle=\int_\Omega\langle x^*(\omega),x(\omega)\rangle\,d\mathbb P(\omega)$ with $x^*\in\Lambda_1(X^*)$) and $v^\circ$ is singular relative to $\mathbb P$, and moreover
--   $$\|v^*\|_{(L^\infty_{\mathbb P}(\Omega,X))^*}=\|v^a\|_{(L^\infty_{\mathbb P}(\Omega,X))^*}+\|v^\circ\|_{(L^\infty_{\mathbb P}(\Omega,X))^*}.$$
--
--   This Yosida–Hewitt-type result is what turns the abstract multiplier of Lemma 3.7 into an integrable random multiplier plus a singular part.
--
--   **Formalization Note** Stated in the paper citing Ioffe–Levin [24, Appendix 1, Theorem 3] and [30]. Uniqueness is stated as uniqueness among all pairs (absolutely continuous, singular) summing to $v^*$; the norm identity is a property of the decomposition. The integrand $x^*$ is not claimed unique.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 21, Theorem 3.9 (stated in this paper, citing [24, Appendix 1, Theorem 3] and [30]); definitions (55), Λ∘(X∗), Λ₁(X∗) on p. 21

import Mathlib
import Definitions.Def_ChanceStateCtrl_AlmostSure_Setting

open MeasureTheory

namespace ChanceStateCtrl.AlmostSure

/-- Theorem 3.9 (Ioffe and Levin), p. 21, stated in this paper citing [24, Appendix 1, Theorem 3]
and [30]. Let `X` be a separable Banach space and `P` a probability measure. Every
`v* ∈ (L∞_P(Ω, X))*` decomposes as `v* = vᵃ + v°` with `vᵃ` absolutely continuous, `v°` singular
relative to `P`, and `‖v*‖ = ‖vᵃ‖ + ‖v°‖`; and the decomposition into an absolutely continuous
and a singular part is unique. -/
theorem theorem_3_9 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] (v : StrongDual ℝ (Lp X ⊤ P)) :
    (∃ va vs : StrongDual ℝ (Lp X ⊤ P), IsAbsCont P va ∧ IsSingular P vs ∧ v = va + vs ∧
        ‖v‖ = ‖va‖ + ‖vs‖) ∧
      ∀ va vs va' vs' : StrongDual ℝ (Lp X ⊤ P), IsAbsCont P va → IsSingular P vs →
        IsAbsCont P va' → IsSingular P vs' → v = va + vs → v = va' + vs' →
        va = va' ∧ vs = vs' := by sorry

end ChanceStateCtrl.AlmostSure
