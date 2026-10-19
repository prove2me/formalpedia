-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornFiberStabilizer_signStab_card_mul_two_pow_nonzero
-- name    : BookProof.ChapterFreeFieldBornFiberStabilizer.signStab_card_mul_two_pow_nonzero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:30:53.054004+00:00
-- url     : https://prove2.me/theorems/899a40b1-8713-40af-90f0-5c134ee18dae
-- title:
--   `BookProof.ChapterFreeFieldBornFiberStabilizer.signStab_card_mul_two_pow_nonzero` (x : EuclideanSpace ℝ (Fin n)) : (signStab x).card * 2 ^ (Finset.univ.filter (fun k => x k ≠ 0)).c
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornFiberStabilizer`.
--
--   `BookProof.ChapterFreeFieldBornFiberStabilizer.signStab_card_mul_two_pow_nonzero` (x : EuclideanSpace ℝ (Fin n)) : (signStab x).card * 2 ^ (Finset.univ.filter (fun k => x k ≠ 0)).card = 2 ^ n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornFiberStabilizer.signStab_card_mul_two_pow_nonzero`.

-- Generated from ChapterFreeFieldBornFiberStabilizer.lean — theorem BookProof.ChapterFreeFieldBornFiberStabilizer.signStab_card_mul_two_pow_nonzero
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornQuotient
import Definitions.Def_ChapterFreeFieldBornSignGauge
import Definitions.Def_ChapterFreeFieldBornFiberCardGeneral
import Definitions.Def_ChapterFreeFieldBornFiberBounds
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberStabilizer
open BookProof.ChapterFreeFieldBornFiberStabilizer


open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornQuotient
open BookProof.ChapterFreeFieldBornSignGauge
open BookProof.ChapterFreeFieldBornFiberCardGeneral
open BookProof.ChapterFreeFieldBornFiberBounds


variable {n : ℕ}

theorem BookProof.ChapterFreeFieldBornFiberStabilizer.signStab_card_mul_two_pow_nonzero (x : EuclideanSpace ℝ (Fin n)) :
    (signStab x).card * 2 ^ (Finset.univ.filter (fun k => x k ≠ 0)).card = 2 ^ n := by sorry
