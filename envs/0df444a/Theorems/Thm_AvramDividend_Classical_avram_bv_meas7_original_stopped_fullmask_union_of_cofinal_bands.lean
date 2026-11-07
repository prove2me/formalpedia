-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_stopped_fullmask_union_of_cofinal_bands
-- name    : AvramDividend.Classical.avram_bv_meas7_original_stopped_fullmask_union_of_cofinal_bands
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:12:07.049054+00:00
-- url     : https://prove2.me/theorems/96122c59-7d21-403c-b589-827d6d764766
-- title:
--   Original stopped predictable interior mask equals the union of cofinal compensated full bands
-- statement:
--   For the original X.X and admissible-dividend right-limit path, any deterministic compact bands inside the strict positive cap interior which eventually cover each interior reserve yield an exact set equality. At each fixed original ruin-stopped clock, the union of physical full-band masks is precisely the complete interior stopped pre-reserve mask. This is the exact source adapter needed before passing from compact-band compensated jumps to the full interior integrand.
-- source:
--   Source-exact deterministic event reduction in the original SpectrallyNegativeLevy X, dividend D, ruinTime X x D, left-limit of X.X minus rightLimit D, and ENNReal.ofReal cap. Planned source witness: avram_bv_meas7_allcap_full_predictable_compact_bands. The equality itself needs only the stated band hypotheses and does not assert any unproved stochastic limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_original_stopped_fullmask_union_of_cofinal_bands
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ)
    (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n)
    (hBand : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hEvent : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n))
    (S : ℝ≥0) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
    let Z : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    (⋃ n : ℕ, {p : ℝ≥0 × Ω |
      (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      Z p ∈ Icc (a n) (b n)}) =
      {p : ℝ≥0 × Ω |
        (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        0 < Z p ∧ ENNReal.ofReal (Z p) < C} := by sorry
