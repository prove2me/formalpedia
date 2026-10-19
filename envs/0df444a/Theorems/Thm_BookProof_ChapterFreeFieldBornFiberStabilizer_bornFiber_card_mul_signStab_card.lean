-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornFiberStabilizer_bornFiber_card_mul_signStab_card
-- name    : BookProof.ChapterFreeFieldBornFiberStabilizer.bornFiber_card_mul_signStab_card
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:31:04.404989+00:00
-- url     : https://prove2.me/theorems/f454e2cd-d037-450c-abfa-f2098c23659b
-- title:
--   `BookProof.ChapterFreeFieldBornFiberStabilizer.bornFiber_card_mul_signStab_card` (x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) : Nat.card ↥(bornMapSphere n ⁻¹' {bornMapSp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornFiberStabilizer`.
--
--   `BookProof.ChapterFreeFieldBornFiberStabilizer.bornFiber_card_mul_signStab_card` (x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) : Nat.card ↥(bornMapSphere n ⁻¹' {bornMapSphere n x}) * (signStab (x : EuclideanSpace ℝ (Fin n))).card = 2 ^ n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornFiberStabilizer.bornFiber_card_mul_signStab_card`.

-- Generated from ChapterFreeFieldBornFiberStabilizer.lean — theorem BookProof.ChapterFreeFieldBornFiberStabilizer.bornFiber_card_mul_signStab_card
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

theorem BookProof.ChapterFreeFieldBornFiberStabilizer.bornFiber_card_mul_signStab_card
    (x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    Nat.card ↥(bornMapSphere n ⁻¹' {bornMapSphere n x}) *
        (signStab (x : EuclideanSpace ℝ (Fin n))).card = 2 ^ n := by sorry
