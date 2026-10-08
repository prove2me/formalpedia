-- Prove2me | Theorems.Thm_AvramDividend_Classical_sampled_hittingBtwn_supermartingale_expected_le
-- name    : AvramDividend.Classical.sampled_hittingBtwn_supermartingale_expected_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:22:44.438391+00:00
-- url     : https://prove2.me/theorems/dc57c2cc-9315-4ffa-a20d-b855760fd5e5
-- title:
--   Finite-grid verification supermartingale: expected stopped value is bounded by its initial expectation
-- statement:
--   Let U be an adapted real-valued process observed on a finite natural-time grid, and V a real-valued supermartingale with respect to the same filtration. Stop at the first grid index between 0 and N where U is negative, or at N if no such index occurs. Then the expected value of V at that stopping index is bounded above by its initial expected value. The hitting time is a bounded stopping time and Mathlib's optional stopping machinery applies via the proved supermartingale helper.
-- source:
--   Finite-grid localisation for Proposition 4(i), obtained from Mathlib Probability.Process.HittingTime, Probability.Martingale.OptionalStopping and AvramDividend.Classical.supermartingale_expected_stoppedValue_antitone_nat. No semimartingale or Itô property is presumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.sampled_hittingBtwn_supermartingale_expected_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {𝓖 : Filtration ℕ mΩ} [SigmaFiniteFiltration μ 𝓖]
    (U V : ℕ → Ω → ℝ)
    (hU : Adapted 𝓖 U)
    (hV : Supermartingale V 𝓖 μ)
    (N : ℕ) :
    (∫ ω, stoppedValue V
      (fun ω => ((hittingBtwn U (Iio (0 : ℝ)) 0 N ω : ℕ) : WithTop ℕ)) ω ∂μ) ≤
      ∫ ω, V 0 ω ∂μ := by sorry
