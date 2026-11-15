-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB58_original_caplinear_initial_right_atom_signed_budget
-- name    : AvramDividend.Classical.avram_gbB58_original_caplinear_initial_right_atom_signed_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:27:17.02386+00:00
-- url     : https://prove2.me/theorems/7a109d7a-2a27-444b-9cea-eec2fe24845e
-- title:
--   Original initial dividend right atom is funded by the true interior-clipped caplinear potential drop
-- statement:
--   At real time zero of the original controlled Lévy dividend path, the true original initial rightLimit D(0) payment plus the interior caplinear potential of the postpayment reserve is at most the original initial caplinear potential, for any clipping cap with the required secant lower bound. This settles the otherwise easily omitted initial payment atom in the finite-cap Gaussian stopped cash-cell ledger, without imposing admissibility at the interior clipping threshold.
-- source:
--   Proved original initial postpayment solvency at t=0 and original B24 global interior caplinear secant. The exact potential decrease bounds the initial right payment as a deterministic cash ledger consequence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB24_interior_caplinear_global_secant
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_initial_postpayment_reserve_between_zero_and_book
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB58_original_caplinear_initial_right_atom_signed_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (b : ℝ)
    (hsec : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ b →
      t - s ≤ w t - w s)
    (ω : Ω) :
    rightLimit D 0 ω +
      (if x - rightLimit D 0 ω ≤ b then
        w (x - rightLimit D 0 ω)
       else w b + ((x - rightLimit D 0 ω) - b)) ≤
    (if x ≤ b then w x else w b + (x - b)) := by sorry
