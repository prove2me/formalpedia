-- Prove2me | Theorems.Thm_AvramDividend_Classical_finitecap_jump_discounted_clipped_driver_mesh_upper_limit
-- name    : AvramDividend.Classical.finitecap_jump_discounted_clipped_driver_mesh_upper_limit
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T08:05:39.144457+00:00
-- url     : https://prove2.me/theorems/e05dc1d5-9034-5fa2-a33a-7305d821b4b1
-- title:
--   Upper limit of discounted frozen-dividend driver increments at a finite ruin-clipped clock
-- statement:
--   In the finite-cap, unbounded-variation jump model, clip an equispaced deterministic mesh at the ruin-clipped horizon. At each cell start hold the paid-dividend balance fixed while moving the surplus driver over the cell. Compute the resulting candidate increment with left discount and the linear continuation of slope one above the cap. Add the change of discount applied to the actual book reserve at the cell end. For a clock at ruin the final book reserve is prepayment, and for a surviving clock or a zero clock it is postpayment.
--
--   Show that the finite sums of these increments are integrable and that their expected upper excess tends to zero. This is the generator estimate for the surplus and discount. No Stieltjes cash integral, terminal payoff bound, or dividend variation term appears in the conclusion.
-- source:
--   Avram, Palmowski and Pistorius (2007), Section 5.4, equation (5.11) and Proposition 4(i), https://arxiv.org/pdf/math/0702893#page=19. Finite-grid surplus and discount terms.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section
open Filter

theorem AvramDividend.Classical.finitecap_jump_discounted_clipped_driver_mesh_upper_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (hFinite : C ≠ ⊤) :
  let V : ℝ → ℝ := fun z => if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
  let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
  let dPaid : ℝ≥0 → Ω → ℝ := fun t ω =>
    if t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω then rightLimit D t ω else D t ω
  let Y : ℝ≥0 → Ω → ℝ := fun t ω => x + X.X t ω - dPaid t ω
  let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let g : ℕ → ℕ → Ω → ℝ≥0 := fun m i ω => min ((i : ℝ≥0) * Δ m) (τ ω)
  let cell : ℝ≥0 → ℝ≥0 → Ω → ℝ := fun s t ω =>
    (E t - E s) * V (Y t ω) +
      E s * (V (x + X.X t ω - dPaid s ω) - V (Y s ω))
  let Source : ℕ → Ω → ℝ := fun m ω => ∑ i ∈ Finset.range (m + 1),
    cell (g m i ω) (g m (i + 1) ω) ω
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
    Integrable (Source m) P ∧ (∫ ω, Source m ω ∂P) ≤ ε := by sorry
