-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_virtualcap_mesh_quadratic
-- name    : AvramDividend.Classical.avram_gledger20_original_strict_prefix_virtualcap_mesh_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T10:52:03.320379+00:00
-- url     : https://prove2.me/theorems/6530056f-8c63-4300-849c-e1fe8911b12b
-- title:
--   Original strict-prefix Gaussian mesh gets artificial-cap quadratic source bound without floor assumptions
-- statement:
--   For actual original-process finite mesh cells wholly before the compact stop, a pointwise prepayment lower reserve floor and monotonic right-limit dividends imply both starting postpayment reserve and frozen-dividend endpoint reserve lie above the same floor. Applying the virtual-ceiling quadratic glue then bounds the exact discounted X.X frozen-source mesh by Gaussian quadratic energy. The theorem removes the otherwise unproved frozen-reserve floor premise on all strictly preterminal cells, including the zero cell. A final cell that ends at the stopping clock is deliberately excluded and requires separate prepayment and strict-cash endpoint accounting in Open 47174f6c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_top_virtualcap_source_mesh_quadratic

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_gledger20_original_strict_prefix_virtualcap_mesh_quadratic
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u b L : ℝ) (hub : u < b) (hL : 0 ≤ L)
    (hwcont : ContinuousOn w (Icc u b))
    (hwderiv : ∀ y ∈ Ioo u b, HasDerivAt w (deriv w y) y)
    (hgrad : ∀ y ∈ Ico u b, 1 ≤ deriv w y)
    (hquad : ∀ y ∈ Ico u b, ∀ z ∈ Icc u b,
      w z ≤ w y + deriv w y * (z - y) + L / 2 * (z - y) ^ 2)
    (q : ℝ) (ω : Ω) (ρ : ℝ≥0)
    (hprefix : ∀ r : ℝ≥0, 0 < r → r < ρ →
      u ≤ riskProcess X x D r ω)
    (S : Finset ℕ) (s t : ℕ → ℝ≥0)
    (hclock : ∀ i ∈ S, s i ≤ t i ∧ t i < ρ) :
    let V : ℝ → ℝ := fun y => if y ≤ b then w y else w b + (y - b)
    let g : ℝ → ℝ := fun y => if y < b then deriv w y else 1
    let Y : ℕ → ℝ := fun i =>
      x + X.X (s i) ω - rightLimit D (s i) ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (t i) ω - rightLimit D (s i) ω
    (∑ i ∈ S, Real.exp (-(q * (t i : ℝ))) *
      (V (Z i) - V (Y i) - g (Y i) * (Z i - Y i))) ≤
      L / 2 * (∑ i ∈ S, Real.exp (-(q * (t i : ℝ))) * (Z i - Y i) ^ 2) := by sorry
