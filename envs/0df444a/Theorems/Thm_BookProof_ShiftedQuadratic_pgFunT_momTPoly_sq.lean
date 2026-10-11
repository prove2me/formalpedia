-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadratic_pgFunT_momTPoly_sq
-- name    : BookProof.ShiftedQuadratic.pgFunT_momTPoly_sq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T12:43:57.982266+00:00
-- url     : https://prove2.me/theorems/672ac10a-2827-488b-b397-a4397649b055
-- title:
--   `BookProof.ShiftedQuadratic.pgFunT_momTPoly_sq` (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) : pgFunT a k (momTPoly k i (momTPoly k i p)) x = -deriv (fun t : ℝ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticEsa`.
--
--   `BookProof.ShiftedQuadratic.pgFunT_momTPoly_sq` (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) : pgFunT a k (momTPoly k i (momTPoly k i p)) x = -deriv (fun t : ℝ => deriv (fun s : ℝ => pgFunT a k p (sec i x s)) t) (x i)
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadratic.pgFunT_momTPoly_sq`.

-- Generated from ChapterShiftedQuadraticEsa.lean — theorem BookProof.ShiftedQuadratic.pgFunT_momTPoly_sq
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

theorem BookProof.ShiftedQuadratic.pgFunT_momTPoly_sq (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFunT a k (momTPoly k i (momTPoly k i p)) x
      = -deriv (fun t : ℝ => deriv (fun s : ℝ => pgFunT a k p (sec i x s)) t) (x i) := by sorry
