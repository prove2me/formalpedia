-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_NSFullData_advection_isSymmetricDom
-- name    : BookProof.NavierStokesFlow.FullEsa.NSFullData.advection_isSymmetricDom
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:19:03.198765+00:00
-- url     : https://prove2.me/theorems/662558a4-8e3d-4c5c-a75f-48b8e997eda8
-- title:
--   `BookProof.NavierStokesFlow.FullEsa.NSFullData.advection_isSymmetricDom` (i : Fin 3) : IsSymmetricDom (d.advection i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullEsa`.
--
--   `BookProof.NavierStokesFlow.FullEsa.NSFullData.advection_isSymmetricDom` (i : Fin 3) : IsSymmetricDom (d.advection i)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FullEsa.NSFullData.advection_isSymmetricDom`.

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.NSFullData.advection_isSymmetricDom
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterSirkFinitePrecision
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa


open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

theorem BookProof.NavierStokesFlow.FullEsa.NSFullData.advection_isSymmetricDom (i : Fin 3) : IsSymmetricDom (d.advection i) := by sorry
