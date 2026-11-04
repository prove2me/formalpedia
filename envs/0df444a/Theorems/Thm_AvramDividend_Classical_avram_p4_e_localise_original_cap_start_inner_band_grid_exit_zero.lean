-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_cap_start_inner_band_grid_exit_zero
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_cap_start_inner_band_grid_exit_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:55:50.944896+00:00
-- url     : https://prove2.me/theorems/5c4bb464-106d-463b-91aa-f0cac6981367
-- title:
--   Original unpaid cap-start forces every sampled strict subcap exit clock to be zero
-- statement:
--   For an original admissible cap-constrained Lévy dividend control starting at the cap c with no immediate right dividend, an observation grid containing t=0 has source postpayment reserve exactly c. Any strict subcap upper band is exited at that first grid point, so the sampled infimum first-exit clock, clipped at any finite nonnegative horizon, is exactly zero. This explicitly identifies why a sequence of strict positive interior-band grid clocks cannot cofinally exhaust a positive ruin time at an unpaid cap start. The result is conditional on such an admissible control and asserts no existence or probabilistic typicality.
-- source:
--   Original source SpectrallyNegativeLevy.X_zero and dividend rightLimit definitions; exact original interior-band clock used by Proved 31bcca2b-9c2e-4494-a223-83dd35a162a9; 3 November 2026 source inspection.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An unpaid cap-start makes every strict-subcap sampled first-exit clock zero. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_cap_start_inner_band_grid_exit_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (c x : ℝ) (hc : 0 < c) (hxc : x = c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (hNoInitialPayment : rightLimit D 0 ω = 0)
    (r : ℕ → ℝ≥0) (hr0 : r 0 = 0)
    (lower upper : ℝ) (hUpper : upper < c)
    (B : ℝ≥0) :
    min (⨅ k : ℕ,
      if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
         upper < x + X.X (r k) ω - rightLimit D (r k) ω
      then (r k : WithTop ℝ≥0) else ⊤) (B : WithTop ℝ≥0)
      = (0 : WithTop ℝ≥0) := by sorry
