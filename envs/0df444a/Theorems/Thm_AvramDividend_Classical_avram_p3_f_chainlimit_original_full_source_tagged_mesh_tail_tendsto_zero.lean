-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_full_source_tagged_mesh_tail_tendsto_zero
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_full_source_tagged_mesh_tail_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:41:44.867187+00:00
-- url     : https://prove2.me/theorems/59bbb211-3be1-42fc-8083-f1e0320a1e0a
-- title:
--   Full original BV tagged C1 mesh source tail vanishes from marked Y and unmarked J controls
-- statement:
--   On a physical original BV Lévy source sample, finite marked negative-jump time sets varying across deterministic grids are injectively right-cell tagged. The actual unmarked negative-jump source mass tends to zero by F28, and a separately verified marked jump-removed Y-cell modulus tends to zero. The exact full F13-type tagged source tail, marked |ΔY| plus unmarked |ΔJ|, tends to zero. This proof uses original J monotonicity to handle absolute increments and does not presuppose the stopped chain or generator compensation. P3-G must provide the marked Y modulus from its compact localisation and finite-source truncation.
-- source:
--   Accepted F26/F21 via F28 uniform source unmarked J squeeze, and original monotone J for |ΔJ| plus actual Y marked source modulus.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_uniform_unmarked_J_tail_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_raw_J_monotone
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_full_source_tagged_mesh_tail_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ)
    (hGrid : ∀ k i, i < n k → (u k) i ≤ (u k) (i + 1)) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) s - X.X s ω
        else 0
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      ∀ (T : ℕ → Finset ℝ≥0)
        (hCover : ∀ k, ∀ v ∈ T k, ∃ i : ℕ,
          i < n k ∧ (u k) i < v ∧ v ≤ (u k) (i + 1))
        (hSeparate : ∀ k, ∀ v ∈ T k, ∀ z ∈ T k, ∀ i : ℕ,
          i < n k → (u k) i < v → v ≤ (u k) (i + 1) →
          (u k) i < z → z ≤ (u k) (i + 1) → v = z)
        (hJTail : Tendsto (fun k =>
          J ((u k) (n k)) - J ((u k) 0) -
            (T k).sum (fun v =>
              Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω))
          atTop (nhds 0))
        (hYMarked : ∀ tag : ℕ → ℝ≥0 → ℕ,
          (∀ k, ∀ v ∈ T k,
            tag k v < n k ∧ (u k) (tag k v) < v ∧
              v ≤ (u k) (tag k v + 1)) →
          (∀ k, ∀ v ∈ T k, ∀ z ∈ T k,
            tag k v = tag k z → v = z) →
          Tendsto (fun k =>
            (Finset.range (n k)).sum (fun i =>
              if i ∈ (T k).image (tag k) then
                |Y ((u k) (i + 1)) - Y ((u k) i)|
              else 0)) atTop (nhds 0)),
        ∃ tag : ℕ → ℝ≥0 → ℕ,
          (∀ k, ∀ v ∈ T k,
            tag k v < n k ∧ (u k) (tag k v) < v ∧
              v ≤ (u k) (tag k v + 1)) ∧
          (∀ k, ∀ v ∈ T k, ∀ z ∈ T k,
            tag k v = tag k z → v = z) ∧
          Tendsto (fun k =>
            (Finset.range (n k)).sum (fun i =>
              if i ∈ (T k).image (tag k) then
                |Y ((u k) (i + 1)) - Y ((u k) i)|
              else
                |J ((u k) (i + 1)) - J ((u k) i)|))
            atTop (nhds 0) := by sorry
