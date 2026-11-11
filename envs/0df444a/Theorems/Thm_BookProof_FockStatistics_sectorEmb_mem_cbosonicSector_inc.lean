-- Prove2me | Theorems.Thm_BookProof_FockStatistics_sectorEmb_mem_cbosonicSector_inc
-- name    : BookProof.FockStatistics.sectorEmb_mem_cbosonicSector_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-10T07:02:41.668507+00:00
-- url     : https://prove2.me/theorems/8dc80f5a-4389-42c1-9aed-89f8f97ea6c8
-- title:
--   `BookProof.FockStatistics.sectorEmb_mem_cbosonicSector_inc` (n : ℕ) {x : (Hs.pow n).carrier} (hx : x ∈ sector (bosonicProj Hs n)) : sectorEmb Hs n x ∈ sector (cbosonicProj Hs n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockStatisticsCompletion`.
--
--   `BookProof.FockStatistics.sectorEmb_mem_cbosonicSector_inc` (n : ℕ) {x : (Hs.pow n).carrier} (hx : x ∈ sector (bosonicProj Hs n)) : sectorEmb Hs n x ∈ sector (cbosonicProj Hs n)
--
--   Formalization note: Lean 4 identifier `BookProof.FockStatistics.sectorEmb_mem_cbosonicSector_inc`.
--
--   Replaces the unuploadable node `BookProof_FockStatistics_sectorEmb_mem_cbosonicSector`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterFockStatisticsCompletion.lean — theorem BookProof.FockStatistics.sectorEmb_mem_cbosonicSector_inc
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterFockStatisticsCompletion
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.TensorCore



open BookProof.ReducedEsa
open BookProof.FarisLavine
open BookProof.PermSector
open BookProof.SecondQuantizationCore

noncomputable section

variable {G : Type*} [Group G] [Fintype G] {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]
variable (Hs : IPSpace) (D : Submodule ℂ Hs.carrier) (A : D →ₗ[ℂ] Hs.carrier)
variable [CompleteSpace Hs.carrier] (hdense : Dense (D : Set Hs.carrier))
  (hsym : SymmetricOn D A) (hesa : EssentiallySelfAdjointOn D A)

theorem BookProof.FockStatistics.sectorEmb_mem_cbosonicSector_inc (n : ℕ) {x : (Hs.pow n).carrier}
    (hx : x ∈ sector (bosonicProj Hs n)) : sectorEmb Hs n x ∈ sector (cbosonicProj Hs n) := by sorry
