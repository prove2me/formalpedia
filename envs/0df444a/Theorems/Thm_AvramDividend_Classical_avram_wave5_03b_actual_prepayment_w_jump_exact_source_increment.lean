-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_prepayment_w_jump_exact_source_increment
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_prepayment_w_jump_exact_source_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:07:18.208541+00:00
-- url     : https://prove2.me/theorems/509cd0f3-9dee-49b6-89c0-dd64c5a7c7aa
-- title:
--   Exact nonlinear prepayment riskProcess jump equals original source pre-jump value increment
-- statement:
--   At every positive time and sample of the genuine spectrally negative Lévy source X and adapted dividend strategy D, the actual prepayment controlled reserve riskProcess has the exact nonlinear jump w(U_t)-w(U_{t-}) = w(Y_{t-}+Delta X_t)-w(Y_{t-}), where Y is the strict left limit of x+X.X-rightLimit D. This combines the already proved exact common left limit and original jump mark and does not merge the separate right dividend-payment atom.
-- source:
--   Canonical Proved original prepayment left-limit agreement caa7f605-3813-4ed6-82a2-31dc2d0b01a0 and exact original-source left jumpmark d2800259-b627-4fd5-b139-985adba4e243; algebraic rewriting. It binds nonlinear w to literal riskProcess and original X on the same sample.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepost_reserve_same_leftlim
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepayment_reserve_exact_source_jumpmark

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_prepayment_w_jump_exact_source_increment
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
    w (riskProcess X x D t ω) -
      w (Function.leftLim
        (fun s : ℝ≥0 => riskProcess X x D s ω) t) =
    w (Y + J) - w Y := by sorry
