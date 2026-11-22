-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_original_finiteactivity_true_stopped_marked_mesh_smallmodulus_L1
-- name    : AvramDividend.Classical.avram_freshD_original_finiteactivity_true_stopped_marked_mesh_smallmodulus_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:24:15.832467+00:00
-- url     : https://prove2.me/theorems/c83baa48-cec7-4661-8200-4eb0f10abef9
-- title:
--   Original finite-activity true stopped physical negative-jump cell mesh errors vanish in L1 under small cell modulus
-- statement:
--   With the actual original spectrally negative Lévy process of finite negative jump activity, the genuinely stopped deterministic physical mesh cells (clipped by a right-continuous stopping time σ≤n), and their negative jump marked indices defined from the original path X, any measurable signed cell errors W whose absolute magnitude is uniformly bounded by ε_m→0 on each marked cell sum to an integrable error converging to zero in absolute L1. The majorant is the actual count of all negative Lévy marks on (0,n], now known integrable, not a fabricated deterministic bound. This is a usable finite-activity nonlinear negative-mark mesh error component of the original physical stopped Itô–Stieltjes cash ledger.
-- source:
--   Original Avram Dividend Classical physical cash-excess theorem 242ca5f1, source-faithful finite-activity mark-cell small-modulus argument; combines already-Proved e19df3d9, 7ad3bc4d and 3e3be685 without assuming the root cash budget, generator inequality or an unrelated linear Jfull.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_freshD_original_fullnegative_physical_finite_horizon_count_L1
import Theorems.Thm_AvramDividend_Classical_avram_b244_original_true_stopping_clock_ruinclipped_marked_cell_L1_dom_20261114
import Theorems.Thm_AvramDividend_Classical_avram_b253_original_marked_physical_source_smallmodulus_Poisson_dom_L1_vanish
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_freshD_original_finiteactivity_true_stopped_marked_mesh_smallmodulus_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (marked : ℕ → Ω → Finset ℕ)
    (hmarked : ∀ m ω, marked m ω =
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let grid : ℕ → ℝ≥0 := fun i =>
        min ((i : ℝ≥0) * Δ) (σ ω)
      (by
        classical
        exact (Finset.range (m + 1)).filter (fun i =>
          ∃ u : ℝ≥0, grid i < u ∧ u ≤ grid (i + 1) ∧
            X.X u ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) u ≠ 0)))
    (W : ℕ → Ω → ℕ → ℝ)
    (hMeas : ∀ m, AEStronglyMeasurable
      (fun ω => ∑ i ∈ marked m ω, W m ω i) P)
    (ε : ℕ → ℝ)
    (hεnonneg : ∀ m, 0 ≤ ε m)
    (hεzero : Tendsto ε atTop (𝓝 (0 : ℝ)))
    (hW : ∀ m, ∀ᵐ ω ∂P, ∀ i ∈ marked m ω,
      ‖W m ω i‖ ≤ ε m) :
    (∀ m, Integrable
      (fun ω => ∑ i ∈ marked m ω, W m ω i) P) ∧
    Tendsto
      (fun m => ∫ ω, ‖∑ i ∈ marked m ω, W m ω i‖ ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
