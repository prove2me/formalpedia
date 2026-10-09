-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_NSHashimoto_velCore_symmetricOn
-- name    : BookProof.NavierStokesFlow.NSHashimoto.velCore_symmetricOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T04:58:41.453997+00:00
-- url     : https://prove2.me/theorems/76db59a4-d066-4a3f-9164-a3d29d0f3306
-- title:
--   The Lean 4 theorem `velCore_symmetricOn` in the `ChapterNavierStokesHashimoto` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.NavierStokesFlow.NSHashimoto.velCore_symmetricOn` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterNavierStokesHashimoto.lean — theorem BookProof.NavierStokesFlow.NSHashimoto.velCore_symmetricOn
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterNavierStokesHashimoto
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.NSHashimoto


open Filter Topology



open BookProof.FarisLavine BookProof.HashimotoShiftInvert BookProof.EsaClosure
open BookProof.HermiteGalerkin
open BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.IkebeKato

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.NSHashimoto.velCore_symmetricOn : SymmetricOn (lpFiniteModes Vel) (velCore A c) := by sorry
