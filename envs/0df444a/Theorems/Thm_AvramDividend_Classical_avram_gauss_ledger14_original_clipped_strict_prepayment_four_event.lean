-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gauss_ledger14_original_clipped_strict_prepayment_four_event
-- name    : AvramDividend.Classical.avram_gauss_ledger14_original_clipped_strict_prepayment_four_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T11:04:51.55097+00:00
-- url     : https://prove2.me/theorems/ed0d8024-f59d-44b9-a136-41e9a58af7f5
-- title:
--   Original clipped random stopped grid telescopes to the strictly prepayment reserve
-- statement:
--   For the actual original Lévy process and dividend strategy, every monotone grid clipped at an arbitrary ruin-bounded clock satisfies the exact discounted four-event identity with the true prepayment terminal. The surviving endpoint right-payment correction is present explicitly at every stop, including the final stop-straddling cell, thereby distinguishing strict-before-stop cash from the proved postpayment telescoping identity. No generator or Gaussian hypothesis is added to this algebraic step.
-- source:
--   Algebraic prepayment correction of Proved e92ede42; necessary terminal chronology in original Gaussian positive-clock budget 642de490 and top strict expected upper d65c7756.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_actual_ruin_stopped_random_grid_four_event_endpoint
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gauss_ledger14_original_clipped_strict_prepayment_four_event
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω)
    (τ : Ω → ℝ≥0)
    (hτruin : (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (u : ℕ → ℝ≥0) (hu : Monotone u)
    (hzero : u 0 = 0) (n : ℕ) (hcover : τ ω ≤ u n) :
    let v : ℕ → ℝ≥0 := fun i => min (u i) (τ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    E (τ ω) * w (riskProcess X x D (τ ω) ω) =
      w x + (w (x - rightLimit D 0 ω) - w x) +
      (∑ i ∈ Finset.range n,
        ((E (v (i + 1)) - E (v i)) * w (Y (v i)) +
          E (v (i + 1)) * (w (Z i) - w (Y (v i))) +
          E (v (i + 1)) *
            (w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) +
          E (v (i + 1)) *
            (w (Y (v (i + 1))) -
              w (riskProcess X x D (v (i + 1)) ω)))) +
      E (τ ω) * (w (riskProcess X x D (τ ω) ω) - w (Y (τ ω))) := by sorry
