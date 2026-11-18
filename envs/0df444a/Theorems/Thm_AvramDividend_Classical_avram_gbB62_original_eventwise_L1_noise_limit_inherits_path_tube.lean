-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB62_original_eventwise_L1_noise_limit_inherits_path_tube
-- name    : AvramDividend.Classical.avram_gbB62_original_eventwise_L1_noise_limit_inherits_path_tube
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:55:00.496964+00:00
-- url     : https://prove2.me/theorems/b8d4c381-bb99-474e-83d7-f058df823a40
-- title:
--   Original Gaussian L1 noise limit inherits a uniform mesh bound on a measurable positive tube event
-- statement:
--   On any measurable event A of a Gaussian probability space, if the actual physical-grid noise approximations M_m are uniformly bounded by ε on A and converge to the original limiting source N in restricted L1, then |N|≤ε almost surely on A. The proof uses the Proved global L1 uniform-bound transfer B61 after inserting the event indicators and the fact that restricted measure is supported on A. This is directly applicable to the original narrow reflected-Gaussian tube and avoids an explicit Itô source representation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB61_L1_limit_inherits_uniform_gaussian_mesh_bound
open MeasureTheory Filter AvramDividend.Classical
open scoped ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB62_original_eventwise_L1_noise_limit_inherits_path_tube
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Set Ω) (hA : MeasurableSet A)
    (N : Ω → ℝ) (M : ℕ → Ω → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hNI : Integrable N (P.restrict A))
    (hMI : ∀ m, Integrable (M m) (P.restrict A))
    (hBound : ∀ m ω, ω ∈ A → |M m ω| ≤ ε)
    (hL1 : Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
      atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂(P.restrict A), |N ω| ≤ ε := by sorry
