-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_CanonicalVector_velH_crd
-- name    : BookProof.NavierStokesFlow.CanonicalVector.velH_crd
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-25T03:23:45.868048+00:00
-- url     : https://prove2.me/theorems/29d73856-9a57-4790-bd0f-e0b63bd28f28
-- title:
--   velH_crd
-- statement:
--   Formal statement of `BookProof.NavierStokesFlow.CanonicalVector.velH_crd` from the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNavierStokesCanonicalVector.lean`).
-- source:
--   https://github.com/leonardpedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesCanonicalVector.lean

-- Generated from ChapterNavierStokesCanonicalVector.lean — theorem BookProof.NavierStokesFlow.CanonicalVector.velH_crd
import Mathlib
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesSignedShift
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow.HermiteFarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift.SignedHop
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.CanonicalVector


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ThreeComponent ShiftHamiltonian SignedShift

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.CanonicalVector.velH_crd (x : lpFiniteModes Vel) (γ : Vel) :
    ((velH A c (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A c))) x) :
        L2I Vel) : Vel → ℂ) γ
      = ladFun A c (crd x) γ := by sorry
