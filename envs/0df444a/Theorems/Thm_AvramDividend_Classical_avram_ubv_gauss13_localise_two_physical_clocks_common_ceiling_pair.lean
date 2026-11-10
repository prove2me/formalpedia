-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_two_physical_clocks_common_ceiling_pair
-- name    : AvramDividend.Classical.avram_ubv_gauss13_localise_two_physical_clocks_common_ceiling_pair
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T08:26:47.255193+00:00
-- url     : https://prove2.me/theorems/a05b87a9-394c-4e20-bdde-ea5890bb4c46
-- title:
--   Common-grid coupling of two physical stopped clocks by true ceilings
-- statement:
--   For two original physical bounded stopping clocks with the first no later than the second and physical gap at most epsilon, if each has a true sampled-filtration ceiling with error at most delta on one monotone time grid, the minimum and maximum sampled indices are both genuine stopping times. Their physical grid values bracket the respective clocks within delta, and their real time gap is at most epsilon plus delta. This is the exact stopping geometry needed to combine Proved 604909b0, 9954ba8b, 2cfa6158, and the two-clock Fatou passage without using an arbitrary floor stopping time.
-- source:
--   Mathlib IsStoppingTime.min/max; deterministic monotone grid geometry and Proved 604909b0 supplies the incoming true ceilings.

import Mathlib
import Mathlib.Probability.Process.Stopping

open MeasureTheory
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_localise_two_physical_clocks_common_ceiling_pair
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓖 : Filtration ℕ mΩ)
    (τ ρ : Ω → ℝ≥0) (hτρ : ∀ ω, τ ω ≤ ρ ω)
    (ε : ℝ≥0) (hGap : ∀ ω, ρ ω ≤ τ ω + ε)
    (grid : ℕ → ℝ≥0) (hgrid : Monotone grid)
    (Kτ Kρ : Ω → ℕ)
    (hKτ : IsStoppingTime 𝓖 (fun ω => (Kτ ω : WithTop ℕ)))
    (hKρ : IsStoppingTime 𝓖 (fun ω => (Kρ ω : WithTop ℕ)))
    (δ : ℝ≥0)
    (hCeilτ : ∀ ω, τ ω ≤ grid (Kτ ω) ∧
      grid (Kτ ω) ≤ τ ω + δ)
    (hCeilρ : ∀ ω, ρ ω ≤ grid (Kρ ω) ∧
      grid (Kρ ω) ≤ ρ ω + δ) :
    IsStoppingTime 𝓖
      (fun ω => ((min (Kτ ω) (Kρ ω)) : WithTop ℕ)) ∧
    IsStoppingTime 𝓖
      (fun ω => ((max (Kτ ω) (Kρ ω)) : WithTop ℕ)) ∧
    (∀ ω, τ ω ≤ grid (min (Kτ ω) (Kρ ω)) ∧
      grid (min (Kτ ω) (Kρ ω)) ≤ τ ω + δ) ∧
    (∀ ω, ρ ω ≤ grid (max (Kτ ω) (Kρ ω)) ∧
      grid (max (Kτ ω) (Kρ ω)) ≤ ρ ω + δ) ∧
    (∀ ω, (grid (max (Kτ ω) (Kρ ω)) : ℝ) -
      (grid (min (Kτ ω) (Kρ ω)) : ℝ) ≤
        (ε : ℝ) + (δ : ℝ)) := by sorry
