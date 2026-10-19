-- Prove2me | Theorems.Thm_BookProof_QuantumGravityFock_qgGradedFock_stone_flow
-- name    : BookProof.QuantumGravityFock.qgGradedFock_stone_flow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:38:05.533694+00:00
-- url     : https://prove2.me/theorems/176b6bab-e3d6-453c-ae51-7cd79ab89214
-- title:
--   `BookProof.QuantumGravityFock.qgGradedFock_stone_flow` (omega g : ℕ → ℝ) : ∃ (T : UnboundedSelfAdjoint (lp (fun _ : GradedIdx => ℂ) 2)) (U : ℝ → (lp (fun _ : GradedIdx => ℂ) 2 →L[ℂ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityFock`.
--
--   `BookProof.QuantumGravityFock.qgGradedFock_stone_flow` (omega g : ℕ → ℝ) : ∃ (T : UnboundedSelfAdjoint (lp (fun _ : GradedIdx => ℂ) 2)) (U : ℝ → (lp (fun _ : GradedIdx => ℂ) 2 →L[ℂ] lp (fun _ : GradedIdx => ℂ) 2)), IsSelfAdjointExtension ((lpFiniteModes GradedIdx).subtype.comp (qgGradedHam omega g)) T.op ∧ IsStoneFlow T U
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityFock.qgGradedFock_stone_flow`.

-- Generated from ChapterQuantumGravityFock.lean — theorem BookProof.QuantumGravityFock.qgGradedFock_stone_flow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterFockSecondQuantization
import Mathlib
import Definitions.Def_ChapterQuantumGravityFock
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
open BookProof.EsaClosure
open BookProof.StoneBridge
open BookProof.QuantumGravityFock



open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.FockOfFock BookProof.NavierStokesFlow.FullEsa
open BookProof.FarisLavine BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.HashimotoShiftInvert
open BookProof.FockSecondQuantization

noncomputable section

theorem BookProof.QuantumGravityFock.qgGradedFock_stone_flow (omega g : ℕ → ℝ) :
    ∃ (T : UnboundedSelfAdjoint (lp (fun _ : GradedIdx => ℂ) 2))
      (U : ℝ → (lp (fun _ : GradedIdx => ℂ) 2 →L[ℂ] lp (fun _ : GradedIdx => ℂ) 2)),
      IsSelfAdjointExtension
        ((lpFiniteModes GradedIdx).subtype.comp (qgGradedHam omega g)) T.op ∧ IsStoneFlow T U := by sorry
