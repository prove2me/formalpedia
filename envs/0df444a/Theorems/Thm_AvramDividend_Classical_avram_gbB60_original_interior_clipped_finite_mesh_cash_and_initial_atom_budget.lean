-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB60_original_interior_clipped_finite_mesh_cash_and_initial_atom_budget
-- name    : AvramDividend.Classical.avram_gbB60_original_interior_clipped_finite_mesh_cash_and_initial_atom_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:34:30.931145+00:00
-- url     : https://prove2.me/theorems/5533fcbe-ac59-4057-bf98-bf1cb5d99650
-- title:
--   Original interior-clipped finite dividend physical mesh plus time-zero right atom fits the genuine initial caplinear potential budget
-- statement:
--   For the genuine original dividend strategy admissible at C but caplinear clipping at any interior c, the actual initial dividend right atom plus the initial postpayment caplinear potential and all finite physical-grid signed discounted Stieltjes dividend corrections are bounded above by the original initial caplinear potential V(x). The theorem accounts for initial zero-time atom and every monotone strictly pre-ruin payment cell with no false smaller-cap admissibility assumption. This completes the finite dividend-sign component of the B54 cash-source ledger.
-- source:
--   B58 pays for original time-zero rightLimit D(0) from interior caplinear potential decrease; B57 bounds the total physical finite-cell signed Stieltjes dividend correction by zero. Adding both exact inequalities gives the finite payment ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB57_original_interior_clipped_actual_finite_dividend_mesh_correction_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_gbB58_original_caplinear_initial_right_atom_signed_budget
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_gbB60_original_interior_clipped_finite_mesh_cash_and_initial_atom_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (C : ℝ≥0∞)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (hV : ∀ z : ℝ, V z =
      if z ≤ c then w z else w c + (z - c))
    (hsec : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ c →
      t - s ≤ w t - w s)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ)
    (hPre : ∀ i < n, u (i + 1) = 0 ∨
      (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    rightLimit D 0 ω + V (x - rightLimit D 0 ω) +
      (∑ i ∈ Finset.range n,
        ((∫⁻ s in Ioc (u i : ℝ) (u (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
          V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) -
          V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω))) ≤
      V x := by sorry
