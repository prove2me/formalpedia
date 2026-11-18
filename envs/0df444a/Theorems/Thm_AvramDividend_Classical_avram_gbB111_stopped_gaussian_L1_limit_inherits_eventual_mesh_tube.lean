-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB111_stopped_gaussian_L1_limit_inherits_eventual_mesh_tube
-- name    : AvramDividend.Classical.avram_gbB111_stopped_gaussian_L1_limit_inherits_eventual_mesh_tube
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:10:54.952604+00:00
-- url     : https://prove2.me/theorems/e8af80e4-a972-4780-a471-67fed83df34a
-- title:
--   Stopped Gaussian L1 limit inherits a path-tube bound valid on sufficiently fine meshes
-- statement:
--   The Proved B62 transfers an eventwise uniform bound on every mesh to its restricted L1 source limit. This extension requires the bound only for sufficiently fine meshes m>=m0, allowing the physical stopped grid's final cell to remain inside a slightly longer Brownian tube while discarding finitely many coarse meshes. Reindex the source by m+m0 and use stability of L1 convergence under a fixed shift.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB62_original_eventwise_L1_noise_limit_inherits_path_tube
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB111_stopped_gaussian_L1_limit_inherits_eventual_mesh_tube
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Set Ω) (hA : MeasurableSet A)
    (N : Ω → ℝ) (M : ℕ → Ω → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (m0 : ℕ) (hNI : Integrable N (P.restrict A))
    (hMI : ∀ m, Integrable (M m) (P.restrict A))
    (hBound : ∀ m, m0 ≤ m → ∀ ω, ω ∈ A → |M m ω| ≤ ε)
    (hL1 : Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
      atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂(P.restrict A), |N ω| ≤ ε := by sorry
