-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_public_allcap_book_postpayment_V_eq_w
-- name    : AvramDividend.Classical.avram_jump6_B_public_allcap_book_postpayment_V_eq_w
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:53:44.853208+00:00
-- url     : https://prove2.me/theorems/6300dc74-d09a-4fbd-a726-e4739ebfd3fe
-- title:
--   Public original capped risk and postpayment book agreement with caplinear w
-- statement:
--   For the original same-process admissible dividend strategy and any cap, both the physical controlled reserve and its right-postpayment reserve lie in the cap-linear agreement region where V=w. The finite cap case uses the Proved original real cap invariant and monotone dividend rightLimit; the top cap case follows definitionally. Reconstructs a previously private useful theorem from public Prove2Me dependencies to enable public proof reuse.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_finite_realcap_invariant_all_times
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_public_allcap_book_postpayment_V_eq_w
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0),
      V (riskProcess X x D t ω) =
        w (riskProcess X x D t ω) ∧
      V (x + X.X t ω - rightLimit D t ω) =
        w (x + X.X t ω - rightLimit D t ω) := by sorry
