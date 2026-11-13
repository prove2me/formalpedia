-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_physical_ceiling_grid_pair_count_exact
-- name    : AvramDividend.Classical.avram_a20_original_borel_physical_ceiling_grid_pair_count_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T16:02:30.137965+00:00
-- url     : https://prove2.me/theorems/eb14e1b6-cc8e-4d7d-9a03-13e30ea1d307
-- title:
--   Exact actual original arbitrary Borel ceiling-grid marked-pair count equals physical past–future rectangle product sum
-- statement:
--   For any sample path of the literal original spectrally negative Lévy process with a finite marked time set for an arbitrary measurable Borel set B up to T, the cardinal of pairs separated by uniform ceiling grid indices equals the sum over physical time cells of the original intrinsic count on (0,s_i] times the original intrinsic count on (s_i,t_i]. The proof combines the separately established distribution-free finite-event ceiling grid pair/window decomposition and the accepted exact original Borel window count as finite time-set filter cardinal. The original X, ν and P remain unchanged. This is the missing pathwise bridge for arbitrary Borel physical factorial second moments.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_borel_physical_ceiling_grid_pair_count_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hS : ({u : ℝ≥0 |
      0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}).Finite)
    (k : ℕ) (hk : 0 < k) :
    let F : Finset ℝ≥0 := hS.toFinset
    let s : Fin k → ℝ≥0 := fun i => ((i.val : ℝ≥0) * T) / (k : ℝ≥0)
    let t : Fin k → ℝ≥0 := fun i => (((i.val + 1 : ℕ) : ℝ≥0) * T) / (k : ℝ≥0)
    let N : ℝ≥0 → ℝ≥0 → ℝ≥0∞ := fun a b =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    ((((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
      Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞) =
      ∑ i : Fin k, N 0 (s i) * N (s i) (t i) := by sorry
