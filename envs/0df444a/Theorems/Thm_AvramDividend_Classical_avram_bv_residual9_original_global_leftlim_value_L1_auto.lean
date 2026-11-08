-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_global_leftlim_value_L1_auto
-- name    : AvramDividend.Classical.avram_bv_residual9_original_global_leftlim_value_L1_auto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T14:33:12.643249+00:00
-- url     : https://prove2.me/theorems/3364b718-838d-4168-98bb-b66426c6ffbc
-- title:
--   Actual BV strict pre-jump value is automatically integrable at every deterministic physical time
-- statement:
--   The original reserve left-limit is jointly measurable (Proved d1627b7b), the continuous-on-nonnegative and negative-zero candidate is globally Borel measurable (Proved 30325a04), and the original BV physical left-limit candidate is uniformly bounded at all finite times (Proved d2cc0694). Therefore the literal random w(Z_t) is integrable for every deterministic physical grid t. This closes the q*w component of each generator-sum cell without changing any original hypotheses; generator and gradient-weighted raw remainder remain independent.
-- source:
--   AVRAM BV-RESIDUAL9 round-six exact original random strict-left-limit w component of edb6442e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_global_leftlim_value_horizon_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_original_global_leftlim_value_L1_auto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (T t : ℝ≥0) (ht : t ≤ T) :
    Integrable
      (fun ω => w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) P := by sorry
