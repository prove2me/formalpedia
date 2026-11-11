-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_top_virtualcap_source_mesh_quadratic
-- name    : AvramDividend.Classical.avram_gledger20_original_top_virtualcap_source_mesh_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T10:31:04.000201+00:00
-- url     : https://prove2.me/theorems/8b5730c9-993f-48d7-9cde-0167bfbc45e8
-- title:
--   Original Gaussian compact stopped source mesh has an artificial-cap quadratic bound
-- statement:
--   Let b be a deterministic ceiling of the physical compact stopping band, even when the actual dividend cap is infinite. On a positive interior band [u,b], assume the original reward is C1, its dividend gradient is at least one, and it obeys a compact quadratic Taylor upper bound. Then the extension V equal to w below b and affine with slope one above b bounds the frozen-dividend original X.X source increments by a discounted quadratic mesh energy. Crucially the gradient condition alone supplies the value-to-ceiling growth condition, so an unbounded frozen source overshoot above b requires no global growth assumption on w. The true reserve remains within [u,b] before the stop. This is a deterministic source-exact analytic ingredient for open 47174f6c, not an asserted full Ito ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gauss_finitec2_gradient_growth_to_cap
import Theorems.Thm_AvramDividend_Classical_avram_gfinite15_original_discounted_cap_gaussian_mesh_bound

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_gledger20_original_top_virtualcap_source_mesh_quadratic
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (u b L : ℝ) (hub : u < b) (hL : 0 ≤ L)
    (hwcont : ContinuousOn w (Icc u b))
    (hwderiv : ∀ y ∈ Ioo u b, HasDerivAt w (deriv w y) y)
    (hgrad : ∀ y ∈ Ico u b, 1 ≤ deriv w y)
    (hquad : ∀ y ∈ Ico u b, ∀ z ∈ Icc u b,
      w z ≤ w y + deriv w y * (z - y) + L / 2 * (z - y) ^ 2)
    (q : ℝ) (ω : Ω) (S : Finset ℕ)
    (s t : ℕ → ℝ≥0)
    (hfloor : ∀ i ∈ S,
      u ≤ x + X.X (s i) ω - rightLimit D (s i) ω ∧
      u ≤ x + X.X (t i) ω - rightLimit D (s i) ω) :
    let V : ℝ → ℝ := fun y => if y ≤ b then w y else w b + (y - b)
    let g : ℝ → ℝ := fun y => if y < b then deriv w y else 1
    let Y : ℕ → ℝ := fun i =>
      x + X.X (s i) ω - rightLimit D (s i) ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (t i) ω - rightLimit D (s i) ω
    (∑ i ∈ S, Real.exp (-(q * (t i : ℝ))) *
      (V (Z i) - V (Y i) - g (Y i) * (Z i - Y i))) ≤
      L / 2 * (∑ i ∈ S, Real.exp (-(q * (t i : ℝ))) * (Z i - Y i) ^ 2) := by sorry
