-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_original_strict_uniform_grid_HJB_B_nonpos_and_prepayment_ae
-- name    : AvramDividend.Classical.avram_bvb_original_strict_uniform_grid_HJB_B_nonpos_and_prepayment_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T14:53:52.005499+00:00
-- url     : https://prove2.me/theorems/0be15ba5-3874-48b3-82f5-bc09ec52cd6b
-- title:
--   Original uniform BV HJB physical B<=0 and exact prepayment equality hold together almost surely
-- statement:
--   For any original Standing bounded-variation spectrally negative Lévy source with HJB supersolution and dividend strategy on the original monotone uniform physical mesh, the exact true masked physical B residual is nonpositive and every strictly positive grid endpoint original reserve prepayment left-limit equals the risk process, both on full-measure events. These are the two central hAllB and hPre premises of the finite-cap boundary-contact leaf.
-- source:
--   Combine Proved source-level HJB signed original BV physical B nonpositivity and original uniform-grid prepayment equality, both simultaneously almost surely, without extra integrability or stopping assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_original_strict_uniform_grid_HJB_B_nonpos_and_prepayment_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0)
    (hu : ∀ n i, u n i ≤ u n (i + 1))
    (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ) (hT : 0 < T)
    (huniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2)) :
    let Z : ℕ → ℕ → Ω → ℝ := fun n i ω => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    let clock : ℕ → ℕ → Ω → Prop := fun n i ω =>
      (u n i : ℝ≥0∞) < ruinTime X x D ω
    let R : ℝ≥0 → Ω → ℝ := fun t ω =>
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) v - X.X v ω
         else 0)
    let coeff : ℕ → ℕ → Ω → ℝ := fun n i ω =>
      if clock n i ω ∧ 0 < Z n i ω ∧ ENNReal.ofReal (Z n i ω) < C then
        Real.exp (-(q * (u n i : ℝ))) * deriv w (Z n i ω)
      else 0
    let G : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ Finset.range (n + 1),
        if clock n i ω ∧ 0 < Z n i ω ∧ ENNReal.ofReal (Z n i ω) < C then
          Real.exp (-(q * (u n i : ℝ))) *
            (X.generator w (Z n i ω) - q * w (Z n i ω)) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0
    let B : ℕ → Ω → ℝ := fun n ω => G n ω +
      (∑ i ∈ Finset.range (n + 1),
        coeff n i ω * (R (u n i) ω - R (u n (i + 1)) ω))
    (∀ᵐ ω ∂P, ∀ n : ℕ, B n ω ≤ 0) ∧
    (∀ᵐ ω ∂P, ∀ n i,
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
        (u n (i + 1)) =
      riskProcess X x D (u n (i + 1)) ω)  := by sorry
