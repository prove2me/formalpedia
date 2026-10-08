-- Prove2me | Theorems.Thm_BookProof_ChapterSirkPerSystemFlowBound_sirk_scheme_bound
-- name    : BookProof.ChapterSirkPerSystemFlowBound.sirk_scheme_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T21:49:33.730209+00:00
-- url     : https://prove2.me/theorems/33f83072-1b1f-4bbc-b681-4965fbda548a
-- title:
--   `BookProof.ChapterSirkPerSystemFlowBound.sirk_scheme_bound` {X : E →L[ℂ] E} {V : G →L[ℂ] E} {S : Set ℂ} {C Dmin h : ℝ} {m : ℕ} {s : RationalScheme E G} (hs : IsSirkScheme X V S C D
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSirkPerSystemFlowBound`.
--
--   `BookProof.ChapterSirkPerSystemFlowBound.sirk_scheme_bound` {X : E →L[ℂ] E} {V : G →L[ℂ] E} {S : Set ℂ} {C Dmin h : ℝ} {m : ℕ} {s : RationalScheme E G} (hs : IsSirkScheme X V S C Dmin h m s) (hS : numRange X ⊆ S) (flow : E →L[ℂ] E) (hflow : flow = s.psiX) (v : E) (hv : V (V.adjoint v) = v) : ‖flow v - sirkApprox V s.psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSirkPerSystemFlowBound.sirk_scheme_bound`.

-- Generated from ChapterSirkPerSystemFlowBound.lean — theorem BookProof.ChapterSirkPerSystemFlowBound.sirk_scheme_bound
import Definitions.Def_ChapterH4
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
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterH9
import Definitions.Def_ChapterSirkEndToEnd
open BookProof.ChapterH6
open BookProof.ChapterH9
open BookProof.ChapterSirkEndToEnd
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

theorem BookProof.ChapterSirkPerSystemFlowBound.sirk_scheme_bound {X : E →L[ℂ] E} {V : G →L[ℂ] E} {S : Set ℂ} {C Dmin h : ℝ} {m : ℕ}
    {s : RationalScheme E G} (hs : IsSirkScheme X V S C Dmin h m s) (hS : numRange X ⊆ S)
    (flow : E →L[ℂ] E) (hflow : flow = s.psiX) (v : E) (hv : V (V.adjoint v) = v) :
    ‖flow v - sirkApprox V s.psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m := by sorry
