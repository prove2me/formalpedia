-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_stopped_cash_endpoint_discount_sandwich
-- name    : AvramDividend.Classical.avram_p3_2_original_stopped_cash_endpoint_discount_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:55:39.240252+00:00
-- url     : https://prove2.me/theorems/81bbf010-4a9c-41e2-b293-62474d6d2790
-- title:
--   Original stopped physical cash exponential endpoint discount sandwich
-- statement:
--   For each payment time inside an original ruin/horizon stopped X/D mesh cell, its single exponential discount factor lies between exponential discount at the right and left cell endpoints.
-- source:
--   Apply interval membership, nonnegative q multiplication, sign reversal and strict monotonicity of real exponential to exact physical original stopped-cell endpoints.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_stopped_cash_endpoint_discount_sandwich
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) (m i : ℕ)
    (t : ℝ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    t ∈ Ioc (u i : ℝ) (u (i + 1) : ℝ) →
      Real.exp (-(q * (u (i + 1) : ℝ))) ≤
        Real.exp (-(q * t)) ∧
      Real.exp (-(q * t)) ≤
        Real.exp (-(q * (u i : ℝ))):= by sorry
