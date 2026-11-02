-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_positive_time_intrinsic_source_and_right_dividend_chronological_jump_identity
-- name    : AvramDividend.Classical.avram_wave5_03_original_positive_time_intrinsic_source_and_right_dividend_chronological_jump_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T16:01:47.367776+00:00
-- url     : https://prove2.me/theorems/d9b5892d-97a5-45f0-abb2-646d7e711e87
-- title:
--   Exact original positive-time chronological nonlinear chain: Lévy source mark then right-dividend lump sum
-- statement:
--   For every positive time of the same original SpectrallyNegativeLevy X and adapted dividend D, the nonlinear source prepayment left jump plus the subsequent right-dividend w-correction telescopes exactly to w(Y+∆X−∆D⁺)−w(Y). Here Y is the genuine strict left limit of x+X.X−rightLimit D and ∆D⁺=rightLimit D−D at the same time and sample. It imports the canonical Proved 03-B nonlinear source jump and the Proved original source mark/left-limit identities, and excludes the special time-zero atom which is handled separately by 04-B. It is a chronological component of the genuine finite-horizon controlled Ito-Meyer identity, not the stochastic integration theorem.
-- source:
--   Original source right payment convention riskProcess and rightLimit D; Wave5 Chat03-B canonical original nonlinear jump 509cd0f3; Wave4 original prepayment leftlimit and source jumpmark caa7f605/d2800259; the BV/UBV cores ef7e6c20/429e17ca.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_prepayment_w_jump_exact_source_increment
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepost_reserve_same_leftlim
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepayment_reserve_exact_source_jumpmark
open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_positive_time_intrinsic_source_and_right_dividend_chronological_jump_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    let Y : ℝ := Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let J : ℝ :=
      X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t
    let A : ℝ := rightLimit D t ω - D t ω
    (w (riskProcess X x D t ω) -
      w (Function.leftLim
        (fun s : ℝ≥0 => riskProcess X x D s ω) t)) +
      (w (riskProcess X x D t ω - A) - w (riskProcess X x D t ω)) =
      w (Y + J - A) - w Y := by sorry
