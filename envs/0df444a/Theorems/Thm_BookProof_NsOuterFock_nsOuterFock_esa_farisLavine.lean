-- Prove2me | Theorems.Thm_BookProof_NsOuterFock_nsOuterFock_esa_farisLavine
-- name    : BookProof.NsOuterFock.nsOuterFock_esa_farisLavine
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T22:54:46.73558+00:00
-- url     : https://prove2.me/theorems/2861a5aa-c0c5-4134-ac53-cc7b4e4a9f5e
-- title:
--   `BookProof.NsOuterFock.nsOuterFock_esa_farisLavine` : EssentiallySelfAdjointOn (outerFriedDom (nsFamily hB hbv hnu hlam hmu hgg).dim) (dsFibOp (fun n : ℕ => harmFried ((nsFamily hB
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsOuterFockFarisLavine`.
--
--   `BookProof.NsOuterFock.nsOuterFock_esa_farisLavine` : EssentiallySelfAdjointOn (outerFriedDom (nsFamily hB hbv hnu hlam hmu hgg).dim) (dsFibOp (fun n : ℕ => harmFried ((nsFamily hB hbv hnu hlam hmu hgg).dim n)) (nsFamily hB hbv hnu hlam hmu hgg).secExt (nsFamily hB hbv hnu hlam hmu hgg).flK (nsFamily hB hbv hnu hlam hmu hgg).secExt_rel) ∧ ∀ x : outerCore (nsFamily hB hbv hnu hlam hmu hgg).dim, ∃ h : (x : outerFock (nsFamily hB hbv hnu hlam hmu hgg).dim) ∈ outerFriedDom (nsFamily hB hbv hnu hlam hmu hgg).dim, dsFibOp (fun n : ℕ => harmFried ((nsFamily hB hbv hnu hlam hmu hgg).dim n)) (nsFamily hB hbv hnu hlam hmu hgg).secExt (nsFamily hB hbv hnu hlam hmu hgg).flK (nsFamily hB hbv hnu hlam hmu hgg).secExt_rel ⟨(x : outerFock (nsFamily hB hbv hnu hlam hmu hgg).dim), h⟩ = (nsFamily hB hbv hnu hlam hmu hgg).outerHam x
--
--   Formalization note: Lean 4 identifier `BookProof.NsOuterFock.nsOuterFock_esa_farisLavine`.

-- Generated from ChapterNsOuterFockFarisLavine.lean — theorem BookProof.NsOuterFock.nsOuterFock_esa_farisLavine
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterSqSumOuterFamily
import Mathlib
import Definitions.Def_ChapterNsOuterFockFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterLeafGaps
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.HermiteProductCore
open BookProof.QgOuterFockFL



open Finset MvPolynomial
open BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.HermiteProductCore BookProof.QgHermiteOscillator
open BookProof.QgOuterFock BookProof.QgOuterFockFL
open BookProof.QgOuterFockInteractionFL
open BookProof.SqSumOuterFamily

noncomputable section

variable (bv : Fin 3 → ℝ) (nu lam mu gg : ℝ)
variable {bv nu lam mu gg}
variable {B : ℝ} (hB : 0 ≤ B) (hbv : ∀ j, |bv j| ≤ B) (hnu : |nu| ≤ B) (hlam : |lam| ≤ B)
  (hmu : |mu| ≤ B) (hgg : |gg| ≤ B)

theorem BookProof.NsOuterFock.nsOuterFock_esa_farisLavine :
    EssentiallySelfAdjointOn
        (outerFriedDom (nsFamily hB hbv hnu hlam hmu hgg).dim)
        (dsFibOp (fun n : ℕ => harmFried ((nsFamily hB hbv hnu hlam hmu hgg).dim n))
          (nsFamily hB hbv hnu hlam hmu hgg).secExt
          (nsFamily hB hbv hnu hlam hmu hgg).flK
          (nsFamily hB hbv hnu hlam hmu hgg).secExt_rel) ∧
      ∀ x : outerCore (nsFamily hB hbv hnu hlam hmu hgg).dim,
        ∃ h : (x : outerFock (nsFamily hB hbv hnu hlam hmu hgg).dim)
            ∈ outerFriedDom (nsFamily hB hbv hnu hlam hmu hgg).dim,
          dsFibOp (fun n : ℕ => harmFried ((nsFamily hB hbv hnu hlam hmu hgg).dim n))
              (nsFamily hB hbv hnu hlam hmu hgg).secExt
              (nsFamily hB hbv hnu hlam hmu hgg).flK
              (nsFamily hB hbv hnu hlam hmu hgg).secExt_rel
              ⟨(x : outerFock (nsFamily hB hbv hnu hlam hmu hgg).dim), h⟩
            = (nsFamily hB hbv hnu hlam hmu hgg).outerHam x := by sorry
