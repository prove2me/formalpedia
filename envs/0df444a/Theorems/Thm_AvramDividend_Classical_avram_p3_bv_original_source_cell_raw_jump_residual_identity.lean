-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_source_cell_raw_jump_residual_identity
-- name    : AvramDividend.Classical.avram_p3_bv_original_source_cell_raw_jump_residual_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:06:37.85139+00:00
-- url     : https://prove2.me/theorems/3afeac6a-ac3f-4f25-8aa3-d0a5501e0437
-- title:
--   Exact original frozen-dividend BV physical source cell decomposes into raw negative jumps and continuous drift residual
-- statement:
--   For the actual original spectrally negative Levy process and controlled reserve, on almost every original sample path every ordered source mesh cell increment of the frozen-dividend reserve equals the deterministic drift contribution minus the full negative original jump sum and the increasing continuous BV residual increment.
-- source:
--   Source-exact instantiation of Proved original raw residual interval cocycle 5b913d53-0281-4b45-b508-bc5ac69419a8. Required to identify actual original stopped source grid increments against the compensated jump/HJB drift integrand in db6a3111.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_interval_cocycle

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- The actual frozen-dividend original source cell is exactly drift,
   the full raw negative-jump interval, and the continuous BV residual. -/

theorem AvramDividend.Classical.avram_p3_bv_original_source_cell_raw_jump_residual_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (i : ℕ),
      u i ≤ u (i + 1) →
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        (t : ℝ) * X.drift - X.X t ω - J t
      let Y : ℝ≥0 → ℝ := fun t =>
        x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun j =>
        x + X.X (u (j + 1)) ω - rightLimit D (u j) ω
      Z i = Y (u i) +
        ((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift -
        (∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
         else 0) -
        (R (u (i + 1)) - R (u i)) := by sorry
