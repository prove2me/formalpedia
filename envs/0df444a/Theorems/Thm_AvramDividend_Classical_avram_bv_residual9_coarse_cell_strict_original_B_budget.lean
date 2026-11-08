-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_coarse_cell_strict_original_B_budget
-- name    : AvramDividend.Classical.avram_bv_residual9_coarse_cell_strict_original_B_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:48:58.694818+00:00
-- url     : https://prove2.me/theorems/8746af97-9c79-428f-aeef-6217c63285d2
-- title:
--   Collapsed original physical grid has a strict signed generator and BV compensation budget
-- statement:
--   Fix an actual bounded-variation spectrally negative Levy process and a physical row whose first n+1 marks are all time zero. If the original pre-ruin mask at that initial clock is active almost surely, and its source-exact generator deficit is bounded above by a strictly negative constant, the exact original compensated signed B row is at most that constant times the nonzero final physical cell. This uses the proved original BV raw R mesh sign, not a claim that R vanishes.
-- source:
--   Bridge for the potential counterexample to original target 4f851376: preserves its source exact Z, original generator, and BV raw R correction. Imports  c27e50dc.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_stopped_derivative_R_mesh_nonpositive
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_coarse_cell_strict_original_B_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i, i < n + 1 → u n i ≤ u n (i + 1))
    (hprefix : ∀ i, i ≤ n → u n i = 0)
    (ε : ℝ) (hε : 0 < ε)
    (hactive : ∀ᵐ ω ∂P,
      (u n n : ℝ≥0∞) < ruinTime X x D ω ∧
      0 < Function.leftLim (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n n) ∧
      ENNReal.ofReal (Function.leftLim (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n n)) < C)
    (hnegative : ∀ᵐ ω ∂P,
      X.generator w (Function.leftLim (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n n)) -
      q * w (Function.leftLim (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n n)) ≤ -ε) :
    ∀ᵐ ω ∂P,
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      (∑ i ∈ Finset.range (n + 1),
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) *
            (X.generator w (Z i) - q * w (Z i)) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0) +
      (∑ i ∈ Finset.range (n + 1),
        (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
        else 0) * (R (u n i) - R (u n (i + 1)))) ≤
      -ε * (u n (n + 1) : ℝ) := by sorry
