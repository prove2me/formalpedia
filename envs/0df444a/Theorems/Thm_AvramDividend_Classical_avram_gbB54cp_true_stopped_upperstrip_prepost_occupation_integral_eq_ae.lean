-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB54cp_true_stopped_upperstrip_prepost_occupation_integral_eq_ae
-- name    : AvramDividend.Classical.avram_gbB54cp_true_stopped_upperstrip_prepost_occupation_integral_eq_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T15:23:59.866547+00:00
-- url     : https://prove2.me/theorems/9ef3182e-cd98-437f-a346-7d590d4ab345
-- title:
--   Original stopped finite-horizon upper-strip occupation is identical for prepayment and postpayment reserves
-- statement:
--   On every actual original dividend-control sample path, the prepayment riskProcess and postpayment x+X-rightLimit D agree Lebesgue almost everywhere at nonnegative times by a proved original theorem. Their upper-strip indicator functions, masked by the true random stopping clock, therefore have exactly equal Lebesgue integrals on any finite physical horizon (0,n). This sharpens the pre/post occupation bridge from a one-sided bound to equality without assuming the two reserves agree at right-dividend jump times.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB54cp_true_stopped_upperstrip_prepost_occupation_integral_eq_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) (ω : Ω) :
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      if t < (ρ ω : ℝ) ∧
        b < riskProcess X x D (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume) =
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      if t < (ρ ω : ℝ) ∧
        b < x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume) := by sorry
