-- Prove2me | Theorems.Thm_DistributedMWC440_UpperBound_lemma_4_6
-- name    : DistributedMWC440.UpperBound.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T15:26:08.911531+00:00
-- url     : https://prove2.me/theorems/42d00b6e-89bf-422d-876b-2b6edebd9929
-- title:
--   Lemma 4.6 (Gap between the 1st and 2nd arrivals )
-- statement:
--   Let $S$ be any finite nonempty index set, $a_s$ fixed real arrivals, $\beta>0$, and $d\ge0$. The index set may have just one member; its unique center then satisfies the comparison vacuously.
--
--   For independent $\delta_s\sim\operatorname{Exponential}(\beta)$,
--
--   $$
--   \Pr\big[\exists s\in S,\ \forall s'\in S\setminus\{s\},\
--   a_s-\delta_s<a_{s'}-\delta_{s'}-d\big]\ge e^{-\beta d}.
--   $$
--
--   Differences from the source:
--   - encoding: independent exponential draws indexed by centers → a finite product of Mathlib exponential measures on real shifts; reason: this is the same continuous law; the rate is positive and truncation is kept separate
-- source:
--   Yi-Jun Chang, Yanyu Chen, Dipan Dey, Yonggang Jiang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, The Complexity of Distributed Minimum Weight Cycle Approximation, STOC 2027 submission #440 (October 2026), citation basis published; papers/stoc2027-440/source.pdf, Lemma 4.6, printed p. 19 / PDF p. 21.

import Definitions.Def_DistributedMWC440_UpperBound_Operations

open scoped ENNReal
open MeasureTheory ProbabilityTheory
noncomputable section

namespace DistributedMWC440.UpperBound

theorem lemma_4_6 {ι : Type} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (β d : ℝ) (hβ : 0 < β) (hd : 0 ≤ d) :
    ENNReal.ofReal (Real.exp (-β*d)) ≤
      (Measure.pi (fun _ : ι => expMeasure β))
        {δ | ∃ s : ι, ∀ s' : ι, s' ≠ s → a s - δ s < a s' - δ s' - d} := by sorry

end DistributedMWC440.UpperBound
