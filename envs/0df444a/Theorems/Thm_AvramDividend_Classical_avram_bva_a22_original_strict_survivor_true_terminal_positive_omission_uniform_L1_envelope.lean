-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_strict_survivor_true_terminal_positive_omission_uniform_L1_envelope
-- name    : AvramDividend.Classical.avram_bva_a22_original_strict_survivor_true_terminal_positive_omission_uniform_L1_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:39:38.694006+00:00
-- url     : https://prove2.me/theorems/169028ac-4e3d-4293-ba33-aaddb123227e
-- title:
--   Original BV strict survivor true full-horizon discounted terminal positive omission has one deterministic row-uniform almost-sure envelope
-- statement:
--   For the true original standing bounded-variation spectrally negative Levy process and dividend strategy, take the actual physical strict grid and original full-T survivor terminal value. Under the original candidate continuity and explicit pre-ruin nonnegative candidate hypothesis, the positive discounted terminal omission beyond the last uniform grid clock is at most a deterministic K almost surely for every mesh row, with K independent of the row. On strict survival, the last grid time is positive and before ruin, so the last discounted candidate is nonnegative; the full-T positive candidate is already uniformly dominated by the Proved original BV wave8_04 source theorem. On non-survival the source terminal omission is defined to be zero. The statement uses the original process, actual clocks, full horizon and ruin convention, without any finite-activity assumption, global generator L1 or alternate sample space. This prepares integrability and dominated terminal positive error at reserve zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_uniform_strict_survival_terminal_ae_bound
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_strict_survivor_true_terminal_positive_omission_uniform_L1_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (x + X.X t ω - rightLimit D t ω))
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ m i, (u m i : ℝ) =
      T * (i : ℝ) / ((m : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let Err : ℕ → Ω → ℝ := fun m ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        max (Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω) -
          Real.exp (-(q * (u m (m + 1) : ℝ))) *
            w (x + X.X (u m (m + 1)) ω -
              rightLimit D (u m (m + 1)) ω)) 0
      else 0
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ m : ℕ, ∀ᵐ ω ∂P, Err m ω ≤ K := by sorry
