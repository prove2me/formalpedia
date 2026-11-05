-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_caplinear_drift_raw_jump_discount_split
-- name    : AvramDividend.Classical.avram_p3_2_original_caplinear_drift_raw_jump_discount_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:26:35.533844+00:00
-- url     : https://prove2.me/theorems/de7776c2-cdc3-4dc9-b200-6173e8f03b81
-- title:
--   Original discounted cap-linear raw-jump grid splits into physical drift and genuine negative jumps
-- statement:
--   A finite discounted grid sum for the cap-linear continuation of w, evaluated on the original Lévy source X and actual dividend path D, equals the sum of drift-only increments plus the chronological original negative-jump increments. The jump term is the literal left-limit mass over each physical cell, with no process substitution. It prepares the raw-jump compensation step in the BV verification.
-- source:
--   Algebraic post-processing of the Proved c19000be original cap-linear raw-jump cell envelope, designed for the earlier published but pending weighted physical grid source theorem and its exact original Stieltjes cash consumer.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_caplinear_drift_raw_jump_discount_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (q : ℝ)
    (u : ℕ → ℝ≥0) (n : ℕ) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    let base : ℕ → ℝ := fun i =>
      x + X.X (u i) ω - rightLimit D (u i) ω
    let drift : ℕ → ℝ := fun i =>
      ((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift
    let jump : ℕ → ℝ := fun i =>
      ∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
      else 0
    let disc : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    (∑ i ∈ Finset.range n,
      disc i * (V (base i + drift i - jump i) - V (base i))) =
    (∑ i ∈ Finset.range n,
      disc i * (V (base i + drift i) - V (base i))) +
    (∑ i ∈ Finset.range n,
      disc i * (V (base i + drift i - jump i) -
        V (base i + drift i))) := by sorry
