-- Prove2me | Theorems.Thm_BookProof_FockNumberPreservingGap_creVec_eq_sum_of_subset
-- name    : BookProof.FockNumberPreservingGap.creVec_eq_sum_of_subset
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T20:26:47.150491+00:00
-- url     : https://prove2.me/theorems/6950534c-5c28-4b7a-9fa0-a8cf1427d5af
-- title:
--   `BookProof.FockNumberPreservingGap.creVec_eq_sum_of_subset` (v : ℕ →₀ ℂ) (x : FockAlg) {s : Finset ℕ} (h : v.support ⊆ s) : creVec v x = ∑ j ∈ s, v j • creA j x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockNumberPreservingGap`.
--
--   `BookProof.FockNumberPreservingGap.creVec_eq_sum_of_subset` (v : ℕ →₀ ℂ) (x : FockAlg) {s : Finset ℕ} (h : v.support ⊆ s) : creVec v x = ∑ j ∈ s, v j • creA j x
--
--   Formalization note: Lean 4 identifier `BookProof.FockNumberPreservingGap.creVec_eq_sum_of_subset`.

-- Generated from ChapterFockNumberPreservingGap.lean — theorem BookProof.FockNumberPreservingGap.creVec_eq_sum_of_subset
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization
open BookProof.FockNumberPreservingGap


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

theorem BookProof.FockNumberPreservingGap.creVec_eq_sum_of_subset (v : ℕ →₀ ℂ) (x : FockAlg) {s : Finset ℕ}
    (h : v.support ⊆ s) : creVec v x = ∑ j ∈ s, v j • creA j x := by sorry
