-- Prove2me | Theorems.Thm_BookProof_SqSumOuterFamily_SqFamily_secExt_commForm_le
-- name    : BookProof.SqSumOuterFamily.SqFamily.secExt_commForm_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:57:49.774688+00:00
-- url     : https://prove2.me/theorems/7bff5e65-c723-4a01-a33d-6cd1326395d3
-- title:
--   `BookProof.SqSumOuterFamily.SqFamily.secExt_commForm_le` (n : ℕ) (u : (harmFried (F.dim n)).dom) : |commForm (F.secExt n) (harmFried (F.dim n)).op u| ≤ F.flc * quadForm (harmFried
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSqSumOuterFamily`.
--
--   `BookProof.SqSumOuterFamily.SqFamily.secExt_commForm_le` (n : ℕ) (u : (harmFried (F.dim n)).dom) : |commForm (F.secExt n) (harmFried (F.dim n)).op u| ≤ F.flc * quadForm (harmFried (F.dim n)).op u
--
--   Formalization note: Lean 4 identifier `BookProof.SqSumOuterFamily.SqFamily.secExt_commForm_le`.

-- Generated from ChapterSqSumOuterFamily.lean — theorem BookProof.SqSumOuterFamily.SqFamily.secExt_commForm_le
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSqSumFarisLavine
import Mathlib
import Definitions.Def_ChapterSqSumOuterFamily
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterLeafGaps
import Definitions.Def_ChapterQgOuterFockInteractionFL
open BookProof.HermiteProductCore
open BookProof.QgOuterFockFL



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockFullFL
open BookProof.GaussCoreQuadBounds BookProof.SqSumFarisLavine
open BookProof.SqSumOuterFamily

noncomputable section

variable (dim : ℕ → ℕ)
variable (F : SqFamily)

theorem BookProof.SqSumOuterFamily.SqFamily.secExt_commForm_le (n : ℕ) (u : (harmFried (F.dim n)).dom) :
    |commForm (F.secExt n) (harmFried (F.dim n)).op u|
      ≤ F.flc * quadForm (harmFried (F.dim n)).op u := by sorry
