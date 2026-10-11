-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_latticeFullData_hamiltonian_apply
-- name    : BookProof.NavierStokesFlow.FullEsa.latticeFullData_hamiltonian_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T08:13:56.083241+00:00
-- url     : https://prove2.me/theorems/675c74fa-f70c-4105-a574-7a73820b765c
-- title:
--   `BookProof.NavierStokesFlow.FullEsa.latticeFullData_hamiltonian_apply` (v : Fin 15 → LinfZ) (nu : ℝ) (x : (latticeFullData v nu).D) : ((latticeFullData v nu).hamiltonian x : L2Z) =
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullEsa`.
--
--   `BookProof.NavierStokesFlow.FullEsa.latticeFullData_hamiltonian_apply` (v : Fin 15 → LinfZ) (nu : ℝ) (x : (latticeFullData v nu).D) : ((latticeFullData v nu).hamiltonian x : L2Z) = latticeFullHamiltonianCLM v nu (x : L2Z)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FullEsa.latticeFullData_hamiltonian_apply`.

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.latticeFullData_hamiltonian_apply
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa


open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

theorem BookProof.NavierStokesFlow.FullEsa.latticeFullData_hamiltonian_apply (v : Fin 15 → LinfZ) (nu : ℝ)
    (x : (latticeFullData v nu).D) :
    ((latticeFullData v nu).hamiltonian x : L2Z) = latticeFullHamiltonianCLM v nu (x : L2Z) := by sorry
