-- Prove2me | Theorems.Thm_BookProof_SqSumOuterFamily_SqFamily_secExt_core
-- name    : BookProof.SqSumOuterFamily.SqFamily.secExt_core
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T23:39:58.593137+00:00
-- url     : https://prove2.me/theorems/d4d74b9b-a625-4075-af8d-3401d176c975
-- title:
--   `BookProof.SqSumOuterFamily.SqFamily.secExt_core` (n : ℕ) (p : polyGaussCore (d := F.dim n)) (h : (p : L2d (F.dim n)) ∈ (harmFried (F.dim n)).dom) : F.secExt n ⟨(p : L2d (F.dim n))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSqSumOuterFamily`.
--
--   `BookProof.SqSumOuterFamily.SqFamily.secExt_core` (n : ℕ) (p : polyGaussCore (d := F.dim n)) (h : (p : L2d (F.dim n)) ∈ (harmFried (F.dim n)).dom) : F.secExt n ⟨(p : L2d (F.dim n)), h⟩ = F.secHam n p
--
--   Formalization note: Lean 4 identifier `BookProof.SqSumOuterFamily.SqFamily.secExt_core`.

-- Generated from ChapterSqSumOuterFamily.lean — theorem BookProof.SqSumOuterFamily.SqFamily.secExt_core
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

theorem BookProof.SqSumOuterFamily.SqFamily.secExt_core (n : ℕ) (p : polyGaussCore (d := F.dim n))
    (h : (p : L2d (F.dim n)) ∈ (harmFried (F.dim n)).dom) :
    F.secExt n ⟨(p : L2d (F.dim n)), h⟩ = F.secHam n p := by sorry
