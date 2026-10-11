-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadratic_deriv_pgFunT_sec_at
-- name    : BookProof.ShiftedQuadratic.deriv_pgFunT_sec_at
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:43:21.782649+00:00
-- url     : https://prove2.me/theorems/baa0854f-e25a-46d7-bef8-e33a28f44dc1
-- title:
--   `BookProof.ShiftedQuadratic.deriv_pgFunT_sec_at` (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) (t : ℝ) : deriv (fun s : ℝ => pgFunT a k p (sec i x s)) t = pgFunT
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticEsa`.
--
--   `BookProof.ShiftedQuadratic.deriv_pgFunT_sec_at` (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) (t : ℝ) : deriv (fun s : ℝ => pgFunT a k p (sec i x s)) t = pgFunT a k (dPolyT k i p) (sec i x t)
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadratic.deriv_pgFunT_sec_at`.

-- Generated from ChapterShiftedQuadraticEsa.lean — theorem BookProof.ShiftedQuadratic.deriv_pgFunT_sec_at
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.HermiteProductCore
open BookProof.HyperbolicQuadratic
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

theorem BookProof.ShiftedQuadratic.deriv_pgFunT_sec_at (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d)
    (t : ℝ) : deriv (fun s : ℝ => pgFunT a k p (sec i x s)) t
      = pgFunT a k (dPolyT k i p) (sec i x t) := by sorry
