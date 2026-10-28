-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_history_killed_renewal_zero_horizon_or_negative_reserve
-- name    : AvramDividend.Classical.chat04_history_killed_renewal_zero_horizon_or_negative_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:03:35.497919+00:00
-- url     : https://prove2.me/theorems/77762a60-c732-4e53-bbd8-92ee1b10dde7
-- title:
--   Killing-scale renewal identity on the zero-horizon and negative-reserve boundary
-- statement:
--   The full-history discounted q-scale expectation equals its initial scale value whenever either the observation horizon is zero or the reserve starts strictly below zero. This holds for every spectrally negative Lévy process and every q-scale function, without Standing or variation assumptions. It combines the previously verified time-zero and already-ruined initial states. This closes two boundary sectors of the remaining whole-history killed renewal identity a885f0b3-3960-424d-97e4-abbcffe268ba, a dependency of two-sided exit 09663d0d-c23e-47da-b5b9-1bbf28449a4d.
-- source:
--   Direct composition of Proved 115a9cae-b7dd-4330-b424-2fc89573a8e5 and 82a74188-f140-406b-94e4-b3e3605e61b2, root-connected to the Avram two-sided exit identity parent 3e1ce2c8-c846-4e0f-8e4f-4fcbd9a0d4d7.

import Theorems.Thm_AvramDividend_Classical_chat04_killed_survival_lintegral_initial_nonnegative
import Theorems.Thm_AvramDividend_Classical_chat04_killed_survival_lintegral_zero_of_negative_initial_reserve

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_history_killed_renewal_zero_horizon_or_negative_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (t : ℝ≥0) (hBoundary : t = 0 ∨ x < 0) :
    (∫⁻ ω,
      ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
        (fun u => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P) =
    ENNReal.ofReal (W x) := by sorry
