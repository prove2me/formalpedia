-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_ymFockCol_apply
-- name    : BookProof.FockSecondQuantization.ymFockCol_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:01:32.585982+00:00
-- url     : https://prove2.me/theorems/3a647af6-56a1-4bab-9432-4ad8b81142eb
-- title:
--   (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (k j : ℕ) : ymFockCol e fabc k j = inner ℂ (coreBasis e j) (ymHamiltonian (coreRepBasis e) fabc ⟨coreBasis e k,...
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.ymFockCol_apply` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.ymFockCol_apply
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

















































































variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]











open Filter Topology
















open BookProof.YangMillsHermite BookProof.HermiteProductCore
open Filter Topology

theorem BookProof.FockSecondQuantization.ymFockCol_apply (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (k j : ℕ) :
    ymFockCol e fabc k j
      = inner ℂ (coreBasis e j)
          (ymHamiltonian (coreRepBasis e) fabc
            ⟨coreBasis e k, Submodule.subset_span ⟨k, rfl⟩⟩) := by sorry
