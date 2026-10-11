-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadratic_deriv2_pgFunT_sec
-- name    : BookProof.ShiftedQuadratic.deriv2_pgFunT_sec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:43:50.145126+00:00
-- url     : https://prove2.me/theorems/899a0c1f-8f26-4f38-bed4-84ef23e27f78
-- title:
--   `BookProof.ShiftedQuadratic.deriv2_pgFunT_sec` (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) : deriv (fun t : ℝ => deriv (fun s : ℝ => pgFunT a k p (sec i x s))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticEsa`.
--
--   `BookProof.ShiftedQuadratic.deriv2_pgFunT_sec` (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) : deriv (fun t : ℝ => deriv (fun s : ℝ => pgFunT a k p (sec i x s)) t) (x i) = pgFunT a k (dPolyT k i (dPolyT k i p)) x
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadratic.deriv2_pgFunT_sec`.

-- Generated from ChapterShiftedQuadraticEsa.lean — theorem BookProof.ShiftedQuadratic.deriv2_pgFunT_sec
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.HermiteProductCore
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.ShiftedHermiteCore
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.ShiftedQuadratic.deriv2_pgFunT_sec (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => pgFunT a k p (sec i x s)) t) (x i)
      = pgFunT a k (dPolyT k i (dPolyT k i p)) x := by sorry
