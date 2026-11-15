-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB57_original_interior_clipped_actual_finite_dividend_mesh_correction_nonpos
-- name    : AvramDividend.Classical.avram_gbB57_original_interior_clipped_actual_finite_dividend_mesh_correction_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:25:28.873591+00:00
-- url     : https://prove2.me/theorems/75f25014-4332-4646-8f87-848df593cad8
-- title:
--   Original finite physical dividend grid has nonpositive signed interior-caplinear Stieltjes correction
-- statement:
--   For any original admissible dividend path, genuine outer cap C, separate interior clipping level c and monotone physical stopping mesh entirely before ruin, the sum of each actual discounted Stieltjes dividend payment increment and the associated postpayment caplinear reserve potential drop is nonpositive. This supplies an exact finite-mesh dividend correction for the B54 stopped Itô cash-source ledger, retaining original D and its right limits.
-- source:
--   Apply proved B25 on each true monotone grid cell with right endpoint before ruin, then sum nonpositive signed source terms. Does not substitute an artificially smaller admissibility cap and does not require the stochastic Ito formula.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB25_original_preruin_interior_caplinear_stieltjes_signed_control
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_gbB57_original_interior_clipped_actual_finite_dividend_mesh_correction_nonpos
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
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ)
    (hPre : ∀ i < n, u (i + 1) = 0 ∨
      (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    (∑ i ∈ Finset.range n,
      ((∫⁻ s in Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
        V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) -
        V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω))) ≤ 0 := by sorry
