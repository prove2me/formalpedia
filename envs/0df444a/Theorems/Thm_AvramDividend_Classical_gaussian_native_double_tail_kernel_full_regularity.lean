-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_native_double_tail_kernel_full_regularity
-- name    : AvramDividend.Classical.gaussian_native_double_tail_kernel_full_regularity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T15:05:56.114335+00:00
-- url     : https://prove2.me/theorems/aa1771a9-cae6-453f-bc87-a92546c7dbc1
-- title:
--   Native Gaussian Esscher kernel is integrable, continuous and antitone
-- statement:
--   For any spectrally negative Lévy process and positive Esscher parameter, the canonical reflected-jump double-tail kernel used in the Gaussian Volterra equation is Lebesgue integrable, continuous and nonincreasing on positive times and nonnegative there. This supplies the exact native-kernel hypotheses for the Gaussian C1 derivative-resolvent proof.
-- source:
--   Native Lévy truncated-square integrability and sigma-finite reflected jump measure, composed with the proved Gaussian double-tail kernel regularity theorem.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_gaussian_real_double_tail_kernel_full_regularity
import Theorems.Thm_AvramDividend_Classical_gaussian_negative_jump_pushforward_sigmaFinite
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_square_integrable_neg_pushforward
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.gaussian_native_double_tail_kernel_full_regularity
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ : ℝ) (hφ : 0 < φ) :
    let K : ℝ → ℝ := fun t : ℝ =>
      (∫⁻ z : ℝ,
        if 0 < t ∧ t < z then
          ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-(φ * z)))
        else 0 ∂(X.ν.map (fun y : ℝ => -y))).toReal
    Integrable K volume ∧
      ContinuousOn K (Ioi (0 : ℝ)) ∧
      AntitoneOn K (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, 0 < t → 0 ≤ K t) := by sorry
