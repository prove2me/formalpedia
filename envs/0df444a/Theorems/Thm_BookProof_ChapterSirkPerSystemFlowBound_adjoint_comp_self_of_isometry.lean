-- Prove2me | Theorems.Thm_BookProof_ChapterSirkPerSystemFlowBound_adjoint_comp_self_of_isometry
-- name    : BookProof.ChapterSirkPerSystemFlowBound.adjoint_comp_self_of_isometry
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T21:48:34.271411+00:00
-- url     : https://prove2.me/theorems/3a3d5200-a2fe-43f8-a5da-5a62f704408a
-- title:
--   `BookProof.ChapterSirkPerSystemFlowBound.adjoint_comp_self_of_isometry` (V : G →L[ℂ] E) (hV : ∀ x : G, ‖V x‖ = ‖x‖) : V.adjoint.comp V = ContinuousLinearMap.id ℂ G
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSirkPerSystemFlowBound`.
--
--   `BookProof.ChapterSirkPerSystemFlowBound.adjoint_comp_self_of_isometry` (V : G →L[ℂ] E) (hV : ∀ x : G, ‖V x‖ = ‖x‖) : V.adjoint.comp V = ContinuousLinearMap.id ℂ G
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSirkPerSystemFlowBound.adjoint_comp_self_of_isometry`.

-- Generated from ChapterSirkPerSystemFlowBound.lean — theorem BookProof.ChapterSirkPerSystemFlowBound.adjoint_comp_self_of_isometry
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterH9
import Definitions.Def_ChapterSirkEndToEnd
import Definitions.Def_ChapterSirkSpectralGeometry
import Definitions.Def_ChapterSirkPerSystem
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesHashimoto
import Definitions.Def_ChapterNavierStokesDiffHashimoto
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterNavierStokesLagrangianKatoRellich
import Mathlib
import Definitions.Def_ChapterSirkPerSystemFlowBound
open BookProof.ChapterSirkPerSystemFlowBound

variable {E G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]


noncomputable section

open Filter Topology


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH9
open BookProof.ChapterSirkEndToEnd BookProof.ChapterSirkSpectralGeometry
open BookProof.ChapterSirkPerSystem
open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.EsaClosure
open BookProof.YangMillsFriedrichs BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.Starobinsky
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.NSHashimoto
open BookProof.NavierStokesFlow.DiffHashimoto BookProof.NavierStokesFlow.DifferentialL2
open BookProof.NavierStokesFlow.LagrangianEsa BookProof.NavierStokesFlow.LagrangianKatoRellich

theorem BookProof.ChapterSirkPerSystemFlowBound.adjoint_comp_self_of_isometry (V : G →L[ℂ] E) (hV : ∀ x : G, ‖V x‖ = ‖x‖) :
    V.adjoint.comp V = ContinuousLinearMap.id ℂ G := by sorry
