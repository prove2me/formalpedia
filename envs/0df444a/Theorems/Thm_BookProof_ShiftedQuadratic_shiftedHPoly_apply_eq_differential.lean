-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadratic_shiftedHPoly_apply_eq_differential
-- name    : BookProof.ShiftedQuadratic.shiftedHPoly_apply_eq_differential
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:44:25.721838+00:00
-- url     : https://prove2.me/theorems/da5ded48-1a34-425c-8d7d-13eeae867f18
-- title:
--   `BookProof.ShiftedQuadratic.shiftedHPoly_apply_eq_differential` (a k : Vd d) (c b b' : Fin d → ℝ) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) : pgFunT a k (shiftedHPoly a k c b b' p) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticEsa`.
--
--   `BookProof.ShiftedQuadratic.shiftedHPoly_apply_eq_differential` (a k : Vd d) (c b b' : Fin d → ℝ) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) : pgFunT a k (shiftedHPoly a k c b b' p) x = ∑ i, (((c i : ℝ) : ℂ) * (-deriv (fun t : ℝ => deriv (fun s : ℝ => pgFunT a k p (sec i x s)) t) (x i) + (((x i : ℝ) : ℂ) ^ 2 / 4) * pgFunT a k p x) + ((b i : ℝ) : ℂ) * (((x i : ℝ) : ℂ) * pgFunT a k p x) + ((b' i : ℝ) : ℂ) * (-Complex.I * deriv (fun t : ℝ => pgFunT a k p (sec i x t)) (x i)))
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadratic.shiftedHPoly_apply_eq_differential`.

-- Generated from ChapterShiftedQuadraticEsa.lean — theorem BookProof.ShiftedQuadratic.shiftedHPoly_apply_eq_differential
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

theorem BookProof.ShiftedQuadratic.shiftedHPoly_apply_eq_differential (a k : Vd d) (c b b' : Fin d → ℝ)
    (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFunT a k (shiftedHPoly a k c b b' p) x
      = ∑ i, (((c i : ℝ) : ℂ)
            * (-deriv (fun t : ℝ => deriv (fun s : ℝ => pgFunT a k p (sec i x s)) t) (x i)
                + (((x i : ℝ) : ℂ) ^ 2 / 4) * pgFunT a k p x)
          + ((b i : ℝ) : ℂ) * (((x i : ℝ) : ℂ) * pgFunT a k p x)
          + ((b' i : ℝ) : ℂ)
              * (-Complex.I * deriv (fun t : ℝ => pgFunT a k p (sec i x t)) (x i))) := by sorry
