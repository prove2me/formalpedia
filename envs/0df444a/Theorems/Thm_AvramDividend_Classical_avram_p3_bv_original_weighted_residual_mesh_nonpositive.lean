-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_weighted_residual_mesh_nonpositive
-- name    : AvramDividend.Classical.avram_p3_bv_original_weighted_residual_mesh_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:22:22.886431+00:00
-- url     : https://prove2.me/theorems/96f15e04-8645-401a-8acf-e742fb544405
-- title:
--   Original BV residual has nonpositive contribution on any positively weighted finite source mesh
-- statement:
--   For the original spectrally negative bounded-variation Lévy source, the residual R(t)=drift*t-X(t)-sum of actual negative jump magnitudes is almost surely nondecreasing. On every increasing deterministic mesh, every nonnegative sample-dependent weight multiplies the negative residual increment. The entire finite weighted sum is therefore almost everywhere nonpositive, with no assertion that R vanishes and no compensator assumptions.
-- source:
--   Accepted original canonical source residual monotonicity e9d95081; Mathlib Finset.sum_nonpos and sub_nonpos

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- On the original source path, the BV residual remaining after physical
drift and actual negative source jumps has nonnegative increments. It
therefore contributes nonpositively to every positively weighted mesh. -/

theorem AvramDividend.Classical.avram_p3_bv_original_weighted_residual_mesh_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (W : ℕ → Ω → ℝ)
    (hW : ∀ ω (i : ℕ), i < n → 0 ≤ W i ω) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      (∑ i ∈ Finset.range n,
        W i ω * (R (u i) - R (u (i + 1)))) ≤ 0 := by sorry
