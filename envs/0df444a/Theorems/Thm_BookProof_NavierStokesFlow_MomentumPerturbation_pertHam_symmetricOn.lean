-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_MomentumPerturbation_pertHam_symmetricOn
-- name    : BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_symmetricOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T17:45:20.101587+00:00
-- url     : https://prove2.me/theorems/5dfced01-bb45-4697-b13c-7598f4a60166
-- title:
--   `BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_symmetricOn` (c : ι → ℝ) (u w : L2I ι) : SymmetricOn (maxDom c) (pertHam c u w)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesMomentumPerturbation`.
--
--   `BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_symmetricOn` (c : ι → ℝ) (u w : L2I ι) : SymmetricOn (maxDom c) (pertHam c u w)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_symmetricOn`.

-- Generated from ChapterNavierStokesMomentumPerturbation.lean — theorem BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_symmetricOn
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumPerturbation
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumPerturbation




open LpNat BookProof.FarisLavine IkebeKato

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_symmetricOn (c : ι → ℝ) (u w : L2I ι) :
    SymmetricOn (maxDom c) (pertHam c u w) := by sorry
