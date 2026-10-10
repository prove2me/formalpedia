-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_diagUnbounded_hasZeroDeficiencyOn
-- name    : BookProof.NavierStokesFlow.FullEsa.diagUnbounded_hasZeroDeficiencyOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:23:52.857741+00:00
-- url     : https://prove2.me/theorems/88ea7d3a-7f79-4a5f-a44b-33a26088fcc7
-- title:
--   `BookProof.NavierStokesFlow.FullEsa.diagUnbounded_hasZeroDeficiencyOn` : HasZeroDeficiencyOn diagUnboundedData.D diagUnboundedData.hamiltonian
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullEsa`.
--
--   `BookProof.NavierStokesFlow.FullEsa.diagUnbounded_hasZeroDeficiencyOn` : HasZeroDeficiencyOn diagUnboundedData.D diagUnboundedData.hamiltonian
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FullEsa.diagUnbounded_hasZeroDeficiencyOn`.

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.diagUnbounded_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow.DiagonalEsa
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa


open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

theorem BookProof.NavierStokesFlow.FullEsa.diagUnbounded_hasZeroDeficiencyOn :
    HasZeroDeficiencyOn diagUnboundedData.D diagUnboundedData.hamiltonian := by sorry
