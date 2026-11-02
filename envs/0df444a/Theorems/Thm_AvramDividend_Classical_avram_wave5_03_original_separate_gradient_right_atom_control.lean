-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_separate_gradient_right_atom_control
-- name    : AvramDividend.Classical.avram_wave5_03_original_separate_gradient_right_atom_control
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:47:24.165834+00:00
-- url     : https://prove2.me/theorems/2cd50555-c982-414f-b6aa-527b1d3ba42a
-- title:
--   Exact original-source BV/UBV separate gradient floors dominate each admissible chronological right dividend atom
-- statement:
--   For one original spectrally negative Levy path and one actual capped admissible dividend process, the BV C1 and UBV C2 smoothness alternatives together with the separate interior derivative floor w' >= 1 imply every right dividend jump Δ+D at time zero or strictly before ruin is no larger than w(riskProcess)-w(riskProcess-Δ+D). The original admissibility ensures Δ+D≥0, Δ+D≤riskProcess and the source cap, including t=0 through X0=D0=0. The closed-cap secant controls both endpoints including zero and C; no full HJB maximum equality, generator, stochastic chain rule, or global sign of w is assumed. This discharges the root HJB hjump obligation under precisely the separate gradient data consumed by BV and corrected UBV canonical cores.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), finite-horizon controlled right-payment correction. Integrator bridge to BV ef7e6c20-a118-46f0-ac94-5b02204bba49 and corrected UBV 429e17ca-5528-40b5-b593-7c03973d0706. Strengthens Proved HJB-equality atom theorem 1baa9a6d under a distinct weaker source hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_rightJump_decomposition
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_separate_gradient_right_atom_control
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)) := by sorry
