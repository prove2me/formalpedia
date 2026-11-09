-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_small13_original_strategy_compact_HJB_drift_L1
-- name    : AvramDividend.Classical.avram_bv_small13_original_strategy_compact_HJB_drift_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:08:58.02113+00:00
-- url     : https://prove2.me/theorems/72410b7c-2a73-4f51-b9d3-d9a0fcddbef1
-- title:
--   Original BV compact discounted HJB drift integrability under dividend strategy without shifted admissibility
-- statement:
--   For the same original bounded-variation spectrally negative Levy process, the discounted HJB drift is integrable on every predictable compact strictly positive pre-reserve strip under the original dividend strategy alone. No admissibility assumption at a spatially shifted starting surplus is required. This permits positive spatial shifts to regularise a zero original pre-reserve in the finite- and unrestricted-cap stopped source proofs. The theorem keeps explicit finite-time compact Lipschitz, value and derivative bounds; it does not establish global signed-generator L1, a stopped cash ledger or a delta-to-zero limit.

import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_ruin_extension_value_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_levy_negative_mark_sigmaFinite
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_negative_jump_generator_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_BV_compact_HJB_drift_uniform
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_rightCont_predictable_ambient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_discounted_HJB_drift_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_HJB_drift_L1_of_compact_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_small13_original_strategy_compact_HJB_drift_L1
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ}
(X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
(T : ℝ≥0) (x : ℝ)
(D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
(w : ℝ → ℝ) (hw_cont : ContinuousOn w (Set.Ici 0))
(hw_neg : ∀ y < 0, w y = 0)
(q : ℝ) (hq : 0 ≤ q)
(a b L R A : ℝ) (ha : 0 < a) (ha2 : a ≤ 2)
(hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R) (hA : 0 ≤ A)
(hLip : ∀ u ∈ Set.Icc (a / 2) b, ∀ v ∈ Set.Icc (a / 2) b,
  |w u - w v| ≤ L * |u - v|)
(hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
(hDeriv : ∀ y ∈ Set.Icc a b, |deriv w y| ≤ A)
(E : Set (ℝ≥0 × Ω)) (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
(hEregion : ∀ p ∈ E, Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1 ∈ Set.Icc a b) :
Integrable (fun p : ℝ≥0 × Ω => if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) *
    (X.drift * deriv w (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) +
     (∫ z in Set.Iio (0 : ℝ),
        w ((Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) + z) - w (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) ∂X.ν) -
     q * w (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1)) else 0)
  ((((volume : Measure ℝ).restrict (Set.Icc 0 (T : ℝ))).map Real.toNNReal).prod P) := by sorry
