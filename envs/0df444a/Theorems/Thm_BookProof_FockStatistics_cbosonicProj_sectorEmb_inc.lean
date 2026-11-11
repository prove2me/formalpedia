-- Prove2me | Theorems.Thm_BookProof_FockStatistics_cbosonicProj_sectorEmb_inc
-- name    : BookProof.FockStatistics.cbosonicProj_sectorEmb_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-10T06:57:24.665693+00:00
-- url     : https://prove2.me/theorems/6d156544-c1b2-47d3-8c7a-edd1367ee0a0
-- title:
--   `BookProof.FockStatistics.cbosonicProj_sectorEmb_inc` (n : ℕ) (x : (Hs.pow n).carrier) : cbosonicProj Hs n (sectorEmb Hs n x) = sectorEmb Hs n (bosonicProj Hs n x)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockStatisticsCompletion`.
--
--   `BookProof.FockStatistics.cbosonicProj_sectorEmb_inc` (n : ℕ) (x : (Hs.pow n).carrier) : cbosonicProj Hs n (sectorEmb Hs n x) = sectorEmb Hs n (bosonicProj Hs n x)
--
--   Formalization note: Lean 4 identifier `BookProof.FockStatistics.cbosonicProj_sectorEmb_inc`.
--
--   Replaces the unuploadable node `BookProof_FockStatistics_cbosonicProj_sectorEmb`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterFockStatisticsCompletion.lean — theorem BookProof.FockStatistics.cbosonicProj_sectorEmb_inc
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterFockStatisticsCompletion
import Definitions.Def_ChapterMaschkeFiniteGroup
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterWignerLittleGroup
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterMaschkeFiniteGroup
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterWignerOrbitClassification
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.ChapterMaschkeFiniteGroup
open BookProof.TensorCore
open BookProof.ChapterWignerLittleGroup



open BookProof.ReducedEsa
open BookProof.SecondQuantizationCore
open BookProof.PermSector

noncomputable section

variable {G : Type*} [Group G] [Fintype G] {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]
variable (Hs : IPSpace) (D : Submodule ℂ Hs.carrier) (A : D →ₗ[ℂ] Hs.carrier)

theorem BookProof.FockStatistics.cbosonicProj_sectorEmb_inc (n : ℕ) (x : (Hs.pow n).carrier) :
    cbosonicProj Hs n (sectorEmb Hs n x) = sectorEmb Hs n (bosonicProj Hs n x) := by sorry
