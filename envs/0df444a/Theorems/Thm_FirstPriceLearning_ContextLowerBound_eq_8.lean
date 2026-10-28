-- Prove2me | Theorems.Thm_FirstPriceLearning_ContextLowerBound_eq_8
-- name    : FirstPriceLearning.ContextLowerBound.eq_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:34:06.64849+00:00
-- url     : https://prove2.me/theorems/cf0eb937-2d1e-426e-950d-8bfcd209495b
-- title:
--   (8): $R_T \ge \frac{\sqrt{KT}}{16}\exp(-\frac{16KR_T}{3T}-\frac{4(\alpha+1)}{3\alpha}) \ge \frac{\sqrt{KT}}{16e^3}\exp(-\frac{16KR_T}{3T})$
-- statement:
--   Let $\alpha\ge1$, $M\ge1$, $K=(\alpha+1)M\le T$, and let $M$ divide $T$. For a (randomized, non-anticipating) policy $\pi$ let
--   $$R_T=\max_{u\in\{0,1,\dots,\alpha\}^M}\mathbb E_u[R_T(\pi)]$$
--   be its largest expected regret on the hard instances $P^u$ of the proof of Theorem 6, against the block context sequence. Then
--   $$R_T\ \ge\ \frac{\sqrt{KT}}{16}\exp\Big(-\frac{16KR_T}{3T}-\frac{4(\alpha+1)}{3\alpha}\Big)\ \ge\ \frac{\sqrt{KT}}{16e^3}\exp\Big(-\frac{16KR_T}{3T}\Big).$$
--
--   This self-referential inequality, which combines (7) with a Bayesian testing argument, is the core of the lower bound; Theorem 6 follows from it under $K^3\le T$.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 24, eq. (8)

import Mathlib
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Model
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Construction

open MeasureTheory

namespace FirstPriceLearning.ContextLowerBound

theorem eq_8 (M α T : ℕ) (hα : 1 ≤ α) (hM : 0 < M) (hT : (α + 1) * M ≤ T) (hMT : M ∣ T)
    {U : Type} [MeasurableSpace U] (μU : Measure U) [IsProbabilityMeasure μU]
    (π : Policy M (Act M α) U) :
    Real.sqrt ((((α + 1) * M : ℕ) : ℝ) * T) / 16 *
          Real.exp (-(16 * (((α + 1) * M : ℕ) : ℝ) * maxRegret M α T hM μU π / (3 * T))
            - 4 * ((α : ℝ) + 1) / (3 * α)) ≤
        maxRegret M α T hM μU π ∧
      Real.sqrt ((((α + 1) * M : ℕ) : ℝ) * T) / (16 * Real.exp 3) *
          Real.exp (-(16 * (((α + 1) * M : ℕ) : ℝ) * maxRegret M α T hM μU π / (3 * T))) ≤
        Real.sqrt ((((α + 1) * M : ℕ) : ℝ) * T) / 16 *
          Real.exp (-(16 * (((α + 1) * M : ℕ) : ℝ) * maxRegret M α T hM μU π / (3 * T))
            - 4 * ((α : ℝ) + 1) / (3 * α)) := by sorry

end FirstPriceLearning.ContextLowerBound
