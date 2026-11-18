-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB115_original_barrier_stopped_GH_L1_limit_bounded_on_upper_tube
-- name    : AvramDividend.Classical.avram_gbB115_original_barrier_stopped_GH_L1_limit_bounded_on_upper_tube
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:34:43.891068+00:00
-- url     : https://prove2.me/theorems/bfa49029-d3c1-4c13-9f9f-9bc30bd6c316
-- title:
--   Exact original cap-barrier stopped Gaussian G/H martingale source limit is bounded on the short upper tube
-- statement:
--   On an original cap-barrier upper-strip tube, the exact physical-grid G/H martingale coefficients simplify to stopped discounted linear Gaussian noise by B114. The centred path remains controlled at all final crossing endpoints of sufficiently fine meshes, and B113 passes that uniform bound to any restricted L1 limit of the exact original physical source. This is a direct source-faithful martingale limit certificate conditional only on the stated original L1 convergence, cap-barrier tube, and grid identities; it does not assume the stopped cash ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB113_original_stopped_grid_L1_limit_bounded_on_overshoot_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB114_original_barrier_upperstrip_stopped_full_GH_mesh_equals_linear_noise
open MeasureTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB115_original_barrier_stopped_GH_L1_limit_bounded_on_upper_tube
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (A : Set Ω) (hA : MeasurableSet A)
    (m0 : ℕ) (T : ℝ≥0) (s : ℕ → ℕ → ℝ≥0)
    (Δ : ℕ → ℝ≥0)
    (hs : ∀ m, Monotone (s m))
    (hs0 : ∀ m, s m 0 = 0)
    (hstep : ∀ m i, s m (i + 1) = s m i + Δ m)
    (hX0 : ∀ ω, X.X 0 ω = 0)
    (q ε a : ℝ) (hq : 0 ≤ q) (hε : 0 ≤ ε)
    (w : ℝ → ℝ)
    (hUpperTube : ∀ ω, ω ∈ A → ∀ u : ℝ≥0, u ≤ T →
      |X.X u ω| ≤ (1 / 400 : ℝ))
    (hCenteredTube : ∀ m, m0 ≤ m → ∀ ω, ω ∈ A →
      ∀ i, s m i ≤ T + Δ m →
        |X.X (s m i) ω - (s m i : ℝ) * X.c| ≤ ε)
    (v : ℕ → ℕ → ℝ) (M : ℕ → Ω → ℝ)
    (hMdef : ∀ m ω, ω ∈ A →
      let Y : ℕ → ℝ := fun i =>
        (1 / 8 : ℝ) + X.X (s m i) ω -
          rightLimit (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ))
            (s m i) ω
      let Z : ℕ → ℝ := fun i =>
        X.X (s m (i + 1)) ω - X.X (s m i) ω -
          ((s m (i + 1) : ℝ) - (s m i : ℝ)) * X.c
      M m ω = (Finset.range (m + 1)).sum (fun i =>
        (if s m i < T then Real.exp (-(q * (s m i : ℝ))) *
          (if Y i ∈ Icc a (5 / 44 : ℝ) then deriv w (Y i) else 1)
        else 0) * Z i +
        (if s m i < T then (1 / 2 : ℝ) *
          Real.exp (-(q * (s m i : ℝ))) *
          (if Y i ∈ Icc a (5 / 44 : ℝ) then
            iteratedDeriv 2 w (Y i) else 0)
        else 0) * (Z i ^ 2 - v m i)))
    (N : Ω → ℝ) (hNI : Integrable N (P.restrict A))
    (hMI : ∀ m, Integrable (M m) (P.restrict A))
    (hL1 : Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
      atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂(P.restrict A), |N ω| ≤ ε := by sorry
