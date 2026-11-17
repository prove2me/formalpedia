-- Prove2me | Theorems.Thm_AltRegret_Supplement_theorem_9
-- name    : AltRegret.Supplement.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:12:16.032208+00:00
-- url     : https://prove2.me/theorems/a60f9a50-8594-4f82-84fd-9f672efe558d
-- title:
--   Theorem 9 — logarithmic lower bound for OCO
-- statement:
--   For every integer $T\ge1$ and every possibly randomized causal online algorithm on the Euclidean unit ball $B_2(1)$, there is a deterministic oblivious sequence of continuous convex losses $f_1,\ldots,f_T:B_2(1)\to[0,1]$ such that
--   $$
--   \mathbb E_A[\operatorname{Reg}_{\mathrm{Alt}}^T]\ge\frac1{125}\left\lfloor\log_{16}T\right\rfloor.
--   $$
--   The expectation is only over the algorithm's private randomness.
--
--   This gives the exact logarithmic lower bound already in two dimensions.
--
--   Differences from the source:
--   - encoding: a possibly randomized online algorithm A → a measurable causal map from past losses and a private seed with an arbitrary probability law; reason: this is the standard seed representation and the existential loss sequence is outside the seed, so it is deterministic and oblivious
--   - encoding: max over comparators in B₂(1) → a real supremum over the compact ball; reason: continuity and compactness make the supremum finite and attained
-- source:
--   Tao, Zheng, Optimal Alternating Regret for Online Learning and Games, arXiv:2608.24731, Theorem 9, p.12

import Mathlib
import Definitions.Def_AltRegret_Supplement_OnlineAlgorithm

open MeasureTheory

namespace AltRegret.Supplement

/-- **Theorem 9 (Logarithmic lower bound for OCO).** Tao–Zheng,
*Optimal Alternating Regret for Online Learning and Games*, arXiv:2608.24731, Theorem 9,
p.12. Every randomized causal online algorithm on the two-dimensional unit ball has a
deterministic oblivious sequence of continuous convex `[0,1]`-valued losses with expected
alternating regret at least `⌊log₁₆ T⌋/125`.

**Formalization Note.** A randomized algorithm is a measurable causal function of its past
losses and a private seed `ω`; `P` is any probability law of that seed. The existential loss
sequence is outside `ω`, expressing that it is deterministic and oblivious. -/
theorem theorem_9 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : OnlineAlgorithm Ω 2)
    (hA : IsOnlineAlgorithmOn (Metric.closedBall (0 : Point 2) 1) A)
    (T : ℕ) (hT : 1 ≤ T) :
    ∃ f : ℕ → Point 2 → ℝ,
      (∀ t, 1 ≤ t → t ≤ T →
        ContinuousOn (f t) (Metric.closedBall (0 : Point 2) 1) ∧
        ConvexOn ℝ (Metric.closedBall (0 : Point 2) 1) (f t) ∧
        ∀ u ∈ Metric.closedBall (0 : Point 2) 1, f t u ∈ Set.Icc (0 : ℝ) 1) ∧
      (1 : ℝ) / 125 * ⌊Real.logb 16 (T : ℝ)⌋₊ ≤
        expectedWorstAltRegret P (Metric.closedBall (0 : Point 2) 1) A f T := by sorry

end AltRegret.Supplement
