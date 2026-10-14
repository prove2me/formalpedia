-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadratic_momTPoly_eq_smul
-- name    : BookProof.ShiftedQuadratic.momTPoly_eq_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:43:34.534287+00:00
-- url     : https://prove2.me/theorems/409f4b46-c3ab-4de8-8a4a-8a03628953ff
-- title:
--   `BookProof.ShiftedQuadratic.momTPoly_eq_smul` (k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) : momTPoly k i p = (-Complex.I) • dPolyT k i p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticEsa`.
--
--   `BookProof.ShiftedQuadratic.momTPoly_eq_smul` (k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) : momTPoly k i p = (-Complex.I) • dPolyT k i p
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadratic.momTPoly_eq_smul`.

-- Generated from ChapterShiftedQuadraticEsa.lean — theorem BookProof.ShiftedQuadratic.momTPoly_eq_smul
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

theorem BookProof.ShiftedQuadratic.momTPoly_eq_smul (k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momTPoly k i p = (-Complex.I) • dPolyT k i p := by sorry
