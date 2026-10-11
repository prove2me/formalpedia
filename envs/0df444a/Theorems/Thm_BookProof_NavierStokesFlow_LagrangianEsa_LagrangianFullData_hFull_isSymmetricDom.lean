-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_LagrangianFullData_hFull_isSymmetricDom
-- name    : BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hFull_isSymmetricDom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T08:14:53.043192+00:00
-- url     : https://prove2.me/theorems/7943342e-6e4f-43c7-bc63-3cfc1ecccf00
-- title:
--   `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hFull_isSymmetricDom` : IsSymmetricDom L.hFull
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesLagrangianEsa`.
--
--   `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hFull_isSymmetricDom` : IsSymmetricDom L.hFull
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hFull_isSymmetricDom`.

-- Generated from ChapterNavierStokesLagrangianEsa.lean — theorem BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hFull_isSymmetricDom
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterSirkFinitePrecision
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterF7
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa




open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)

theorem BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hFull_isSymmetricDom : IsSymmetricDom L.hFull := by sorry
