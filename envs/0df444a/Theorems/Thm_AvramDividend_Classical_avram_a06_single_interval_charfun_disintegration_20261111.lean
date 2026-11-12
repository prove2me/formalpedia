-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_single_interval_charfun_disintegration_20261111
-- name    : AvramDividend.Classical.avram_a06_single_interval_charfun_disintegration_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:31:13.892545+00:00
-- url     : https://prove2.me/theorems/f622a828-66c5-40a6-a048-ea4f9e235616
-- title:
--   Randomly indexed single marked interval characteristic-function disintegration
-- statement:
--   The one-dimensional Fubini law for a random bounded interval in an independent count grid and mark sequence. This removes the stochastic conditioning from a single interval but does not assume identical mark laws, count monotonicity, or fixed-grid Fourier factorization. Derive from proved independent-stream disintegration and measurable random mark interval.

import Mathlib
open MeasureTheory ProbabilityTheory Finset
noncomputable section

theorem AvramDividend.Classical.avram_a06_single_interval_charfun_disintegration_20261111
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (N : Fin (n + 1) → Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hN : Measurable (fun ω => fun i => N i ω))
    (hY : Measurable (fun ω => fun j => Y j ω))
    (hSeparate : IndepFun (fun ω => fun i => N i ω)
      (fun ω => fun j => Y j ω) P)
    (i : Fin n) (t : ℝ) :
    MeasureTheory.charFun
      (Measure.map (fun ω : Ω =>
        ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω) P) t =
    ∫ ω, MeasureTheory.charFun
      (Measure.map (fun ω' : Ω =>
        ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω') P) t ∂P := by sorry
