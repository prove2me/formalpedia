-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadratic_pgFunT_apply_sum
-- name    : BookProof.ShiftedQuadratic.pgFunT_apply_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:44:01.761405+00:00
-- url     : https://prove2.me/theorems/d41ec18d-e3ee-4967-91a9-15aa6111f0f6
-- title:
--   `BookProof.ShiftedQuadratic.pgFunT_apply_sum` {ι : Type*} (a k : Vd d) (s : Finset ι) (f : ι → MvPolynomial (Fin d) ℂ) (x : Vd d) : pgFunT a k (∑ v ∈ s, f v) x = ∑ v ∈ s, pgFunT a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticEsa`.
--
--   `BookProof.ShiftedQuadratic.pgFunT_apply_sum` {ι : Type*} (a k : Vd d) (s : Finset ι) (f : ι → MvPolynomial (Fin d) ℂ) (x : Vd d) : pgFunT a k (∑ v ∈ s, f v) x = ∑ v ∈ s, pgFunT a k (f v) x
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadratic.pgFunT_apply_sum`.

-- Generated from ChapterShiftedQuadraticEsa.lean — theorem BookProof.ShiftedQuadratic.pgFunT_apply_sum
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.HermiteProductCore
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

theorem BookProof.ShiftedQuadratic.pgFunT_apply_sum {ι : Type*} (a k : Vd d) (s : Finset ι)
    (f : ι → MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFunT a k (∑ v ∈ s, f v) x = ∑ v ∈ s, pgFunT a k (f v) x := by sorry
