-- Prove2me | Theorems.Thm_BookProof_YangMillsAbelianEsa_sum_ymMomVec_mom
-- name    : BookProof.YangMillsAbelianEsa.sum_ymMomVec_mom
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T18:20:18.161625+00:00
-- url     : https://prove2.me/theorems/8fca99f8-7b5a-4154-a815-ccba39f5a8bc
-- title:
--   `BookProof.YangMillsAbelianEsa.sum_ymMomVec_mom` (m : Fin 24) : ∑ n : Fin 99, ((ymMomVec m n : ℝ) : ℂ) • momPoly (d := 99) n = momPoly (ymMomIdx m)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterYangMillsAbelianEsa`.
--
--   `BookProof.YangMillsAbelianEsa.sum_ymMomVec_mom` (m : Fin 24) : ∑ n : Fin 99, ((ymMomVec m n : ℝ) : ℂ) • momPoly (d := 99) n = momPoly (ymMomIdx m)
--
--   Formalization note: Lean 4 identifier `BookProof.YangMillsAbelianEsa.sum_ymMomVec_mom`.

-- Generated from ChapterYangMillsAbelianEsa.lean — theorem BookProof.YangMillsAbelianEsa.sum_ymMomVec_mom
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.YangMillsAbelianEsa



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs

noncomputable section

theorem BookProof.YangMillsAbelianEsa.sum_ymMomVec_mom (m : Fin 24) :
    ∑ n : Fin 99, ((ymMomVec m n : ℝ) : ℂ) • momPoly (d := 99) n
      = momPoly (ymMomIdx m) := by sorry
