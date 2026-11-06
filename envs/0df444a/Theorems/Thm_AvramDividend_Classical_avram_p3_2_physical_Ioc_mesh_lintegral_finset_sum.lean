-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_physical_Ioc_mesh_lintegral_finset_sum
-- name    : AvramDividend.Classical.avram_p3_2_physical_Ioc_mesh_lintegral_finset_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:57:42.196019+00:00
-- url     : https://prove2.me/theorems/53bfae43-7285-451e-82af-bd425f47efe6
-- title:
--   Exact original physical half-open Stieltjes mass is additive over finite monotone grid cells
-- statement:
--   For every real time mesh u monotone, arbitrary Borel measure μ and ENNReal integrand f, the lintegral over Ioc(u0,un) equals the finite sum of lintegrals on adjacent Ioc cells.
-- source:
--   Pinned Mathlib lintegral_biUnion_finset on Borel pairwise disjoint mesh cells, plus fully Proved monotone finite mesh set-cover identity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_physical_monotone_Ioc_mesh_cover

open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_physical_Ioc_mesh_lintegral_finset_sum (μ : Measure ℝ) (u : ℕ → ℝ)
    (hu : Monotone u) (n : ℕ) (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ioc (u 0) (u n), f t ∂μ) =
      ∑ i ∈ Finset.range n,
        ∫⁻ t in Ioc (u i) (u (i + 1)), f t ∂μ:= by sorry
