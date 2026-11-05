-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_mesh_family_true_stopping_converges
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_mesh_family_true_stopping_converges
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:40:15.643276+00:00
-- url     : https://prove2.me/theorems/cd646e2b-18dd-496e-b19e-5b4fc3ffb16f
-- title:
--   One exact family of true bounded original-filtration ceiling stopping times converges pathwise to the source ruin clock
-- statement:
--   Under the actual original dividend strategy, source ruin stopping and a shrinking sequence of grid meshes, there is one family Kk whose each member is a true bounded stopping time on its own sampled right-continuous filtration and whose sampled times e_k(Kk) converge pathwise to the exact min(ruinTime,n).toNNReal. All obligations use one same K family, suitable for bounded martingale optional stopping on each grid and subsequent UI/L1 passage.
-- source:
--   Dependent on new family grid stopping+mesh theorem and the accepted P4-E source NNReal squeeze.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_every_mesh_true_bounded_stopping_and_error
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_grid_clock_squeeze_tendsto

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact original stopped clock is the limit of true bounded stopping ceilings on varying grids. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_mesh_family_true_stopping_converges
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (n : ℕ)
    (e : ℕ → ℕ → ℝ≥0) (he : ∀ k, Monotone (e k))
    (N : ℕ → ℕ) (hN : ∀ k, (n : ℝ≥0) ≤ e k (N k))
    (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (𝓝 0))
    (h0 : ∀ k, e k 0 = 0)
    (hStep : ∀ k i, e k (i + 1) ≤ e k i + δ k)
    (𝓖 : ℕ → Filtration ℕ mΩ)
    (h𝓖 : ∀ k, 𝓖 k =
      ({ seq := fun i : ℕ => 𝓕.rightCont (e k i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (he k hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (e k i) } : Filtration ℕ mΩ)) :
    ∃ K : ℕ → Ω → ℕ,
      (∀ k, IsStoppingTime (𝓖 k)
        (fun ω => (K k ω : WithTop ℕ))) ∧
      (∀ k ω, (K k ω : WithTop ℕ) ≤ (N k : WithTop ℕ)) ∧
      (∀ ω, Tendsto (fun k => e k (K k ω)) atTop
        (𝓝 ((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal))) := by sorry
