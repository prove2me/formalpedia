-- Prove2me | Theorems.Thm_ChanceStateCtrl_Robust_lemma_3_4
-- name    : ChanceStateCtrl.Robust.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:58.469+00:00
-- url     : https://prove2.me/theorems/fb6d1792-0909-4a64-b901-0ead0943aecd
-- title:
--   Lemma 3.4, p. 19 — for lower semicontinuous h, h(ξ) ≤ 0 almost surely iff h ≤ 0 on the support of the law of ξ
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $\xi:\Omega\to\mathbb R^m$ a random vector with a density, and let $\Xi\subseteq\mathbb R^m$ be the support of its law $P\circ\xi^{-1}$. Let $h:\mathbb R^m\to\mathbb R$ be lower semicontinuous. Then
--   $$h(\xi(\omega))\le0\quad P\text{-a.s.}\qquad\Longleftrightarrow\qquad h(z)\le0\quad\forall z\in\Xi.$$
--
--   This is the bridge between almost-sure and robust constraints: under lower semicontinuity in the parameter, the two feasible sets coincide.
--
--   **Formalization Note** "With density" is absolute continuity of the law with respect to Lebesgue measure; it is a hypothesis of the page and is kept though the equivalence does not use it. The support is Mathlib's `Measure.support`, the set of points all of whose neighbourhoods have positive measure (the usual closed support).
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 19, Lemma 3.4

import Mathlib
import Definitions.Def_ChanceStateCtrl_Robust_Setting

open MeasureTheory

namespace ChanceStateCtrl.Robust

theorem lemma_3_4 {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (hdens : P.map ξ ≪ volume) (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : LowerSemicontinuous h) :
    (∀ᵐ w ∂P, h (ξ w) ≤ 0) ↔ ∀ z ∈ (P.map ξ).support, h z ≤ 0 := by sorry

end ChanceStateCtrl.Robust
