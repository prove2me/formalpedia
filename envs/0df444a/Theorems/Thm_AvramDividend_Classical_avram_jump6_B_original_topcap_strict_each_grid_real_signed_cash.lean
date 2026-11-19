-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_topcap_strict_each_grid_real_signed_cash
-- name    : AvramDividend.Classical.avram_jump6_B_original_topcap_strict_each_grid_real_signed_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T21:54:46.937637+00:00
-- url     : https://prove2.me/theorems/ab5ca2a4-e200-486c-b65f-35c9f8d886e6
-- title:
--   Original infinite-activity-compatible top-cap strict-pre-ruin real signed cash bound at every physical mesh
-- statement:
--   Under true original Levy X and admissible D, all-cap positive top limit C and genuine stopped time t strictly before original ruin, for every canonical physical grid j the original closed-Iic discounted cash plus initial signed potential correction minus the real discounted sum of original prepayment potential drops is bounded above by the actual ENNReal Stieltjes mesh error. Derived from Proved original same-X canonical cash upper bound and nonnegative true top-cap drops, the original initial right atom sign, and the public finite real cash conversion lemma. No finite negative jump intensity assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_strict_preruin_stieltjes_discount_cash
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_finite_cash_signed_source_from_true_stieltjes_envelope
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_discount_error_finite_and_vanishing
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anycap_initial_rightpayment_postvalue_budget
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_topcap_canonical_stopped_mesh_all_payment_drops_nonnegative
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_topcap_strict_each_grid_real_signed_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hTop : C = ⊤)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (hStrict : (t : ℝ≥0∞) < ruinTime X x D ω)
    (n : ℕ) (ht : t ≤ (n : ℝ≥0)) :
    let v : ℕ → ℕ → ℝ≥0 := fun j i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    let m : ℕ → ℕ := fun j => (n + 1) * (j + 1)
    let Cash : ℝ≥0∞ :=
      ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (t : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)
    let Err : ℕ → ℝ≥0∞ := fun j =>
      ENNReal.ofReal (q * ((1 : ℝ) / ((j : ℝ) + 1))) *
        dividendMeasure D ω (Ioc (0 : ℝ) (t : ℝ))
    ∀ j, Cash.toReal + (w (x - rightLimit D 0 ω) - w x) -
      (∑ i ∈ Finset.range (m j),
        Real.exp (-(q * (v j (i + 1) : ℝ))) *
        (w (x + X.X (v j (i + 1)) ω - rightLimit D (v j i) ω) -
          w (x + X.X (v j (i + 1)) ω - rightLimit D (v j (i + 1)) ω)))
      ≤ (Err j).toReal := by sorry
