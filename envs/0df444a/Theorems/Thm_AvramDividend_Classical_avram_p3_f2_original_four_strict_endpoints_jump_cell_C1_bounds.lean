-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_four_strict_endpoints_jump_cell_C1_bounds
-- name    : AvramDividend.Classical.avram_p3_f2_original_four_strict_endpoints_jump_cell_C1_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T21:39:29.855908+00:00
-- url     : https://prove2.me/theorems/f2caf6a4-f9e9-4051-a972-aa5258fa81d4
-- title:
--   Original BV all-four strict source jump endpoints automatically yield one uniform C1 jump-pair bound
-- statement:
--   For every nonempty physical grid on the original spectrally negative Lévy path, form literal source J, jump-removed Y, right-reserve z, and increments c and j. If all four genuine negative-jump source reserves z,z+c,z-j,z+c-j are strictly in the positive subcap, the previously proved finite-set interior localisation constructs one common compact interior band for all four families of endpoints. The previously proved original stopped four-pair C1 lemma then gives one nonnegative Lipschitz constant for all four source jump-pair inequalities simultaneously, with no abstract process or assumed compact band. P3-G2 must provide pre-ruin/cap-boundary localisation, not asserted here.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_h_localise_finite_interior_mesh_reserves_common_band
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_stopped_compact_C1_jump_cell_four_pairs
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_four_strict_endpoints_jump_cell_C1_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ) (hn : 0 < n) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    let z : ℕ → ℝ := fun i =>
      x + X.X (u i) ω - rightLimit D (u i) ω
    let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
    let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
    (∀ i, i < n →
      z i ∈ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
      z i + c i ∈ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
      z i - j i ∈ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
      z i + c i - j i ∈ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) →
    ∃ L : ℝ, 0 ≤ L ∧ ∀ i, i < n →
      (|w (z i + c i - j i) - w (z i - j i)| ≤ L * |c i|) ∧
      (|w (z i + c i) - w (z i)| ≤ L * |c i|) ∧
      (|w (z i + c i - j i) - w (z i + c i)| ≤ L * |j i|) ∧
      (|w (z i - j i) - w (z i)| ≤ L * |j i|) := by sorry
