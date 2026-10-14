-- Prove2me | Theorems.Thm_BookProof_YangMillsAbelianEsa_pgLp_eq_pgMap
-- name    : BookProof.YangMillsAbelianEsa.pgLp_eq_pgMap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:33:09.692487+00:00
-- url     : https://prove2.me/theorems/63d85d71-930a-4c95-be98-9683b087362f
-- title:
--   `BookProof.YangMillsAbelianEsa.pgLp_eq_pgMap` (p : MvPolynomial (Fin 99) ℂ) : pgLp p = pgMap (d := 99) p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterYangMillsAbelianEsa`.
--
--   `BookProof.YangMillsAbelianEsa.pgLp_eq_pgMap` (p : MvPolynomial (Fin 99) ℂ) : pgLp p = pgMap (d := 99) p
--
--   Formalization note: Lean 4 identifier `BookProof.YangMillsAbelianEsa.pgLp_eq_pgMap`.

-- Generated from ChapterYangMillsAbelianEsa.lean — theorem BookProof.YangMillsAbelianEsa.pgLp_eq_pgMap
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
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
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductCore
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

theorem BookProof.YangMillsAbelianEsa.pgLp_eq_pgMap (p : MvPolynomial (Fin 99) ℂ) : pgLp p = pgMap (d := 99) p := by sorry
