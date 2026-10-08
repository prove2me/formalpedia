-- Prove2me | Theorems.Thm_AvramDividend_Classical_sampledRiskProcess_hittingBtwn_le_terminal
-- name    : AvramDividend.Classical.sampledRiskProcess_hittingBtwn_le_terminal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T21:13:58.143245+00:00
-- url     : https://prove2.me/theorems/001a9bb2-407a-4e0e-b9f1-8e277e62b9ce
-- title:
--   Finite-grid reserve hitting time is bounded by the terminal index
-- statement:
--   The first negative sampled reserve between grid indices 0 and N is always at most N; if there is no hit, hittingBtwn equals N. This is the uniform boundedness hypothesis required by discrete optional stopping.
-- source:
--   Mathlib Probability.Process.HittingTime, hittingBtwn_mem_Icc; finite-grid localisation helper for Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.sampledRiskProcess_hittingBtwn_le_terminal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (δ : ℝ≥0) (N : ℕ) (ω : Ω) :
    ((hittingBtwn
      (fun k : ℕ => fun ω =>
        riskProcess X x D ((k : ℝ≥0) * δ) ω)
      (Iio (0 : ℝ)) 0 N ω : ℕ) : WithTop ℕ) ≤
      (N : WithTop ℕ) := by sorry
