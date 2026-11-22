-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ripple_original_strict_floor_masked_Hessian_fullcell_public_bound
-- name    : AvramDividend.Classical.avram_ripple_original_strict_floor_masked_Hessian_fullcell_public_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T18:57:01.619813+00:00
-- url     : https://prove2.me/theorems/158df1a6-469a-435e-80f9-b7686005f3cf
-- title:
--   Public original pre-ruin stopped Hessian physical-grid compact bound
-- statement:
--   Prove the exact original stopped finite-cap physical-grid Hessian coefficient uniformly bounded using the public original pre-ruin postpayment reserve floor and compact C2 second derivative bounds.
-- source:
--   Exact remotely Proved source of previously private theorem 87d4f7b6-2b95-4567-ae70-65dda5e44952; source-faithful public re-verification with only public upstream imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_interior_C2_compact_second_derivative_bound

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ripple_original_strict_floor_masked_Hessian_fullcell_public_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (δ b C q : ℝ)
    (hδ : 0 < δ) (hb : 0 < b) (hbC : b < C) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (n m i : ℕ) (ω : Ω),
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        i < m → s < ρ ω → s + Δ ≤ ρ ω →
        |Real.exp (-(q * (s : ℝ))) *
          (if x + X.X s ω - rightLimit D s ω ≤ b
           then iteratedDeriv 2 w (x + X.X s ω - rightLimit D s ω)
           else 0)| ≤ K := by sorry
