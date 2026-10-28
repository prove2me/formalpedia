-- Prove2me | Theorems.Thm_BookProof_HermiteCarleman_mixOp_deficiencyTrivialAt
-- name    : BookProof.HermiteCarleman.mixOp_deficiencyTrivialAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:25:46.400172+00:00
-- url     : https://prove2.me/theorems/25455273-78b3-4d3c-9258-91c0b2b6e21f
-- title:
--   `BookProof.HermiteCarleman.mixOp_deficiencyTrivialAt` (c b b' : Fin d → ℝ) {z : ℂ} (hz : z.im ≠ 0) : DeficiencyTrivialAt (polyGaussCore (d := d)) (mixOp c b b') z
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteCarlemanEsa`.
--
--   `BookProof.HermiteCarleman.mixOp_deficiencyTrivialAt` (c b b' : Fin d → ℝ) {z : ℂ} (hz : z.im ≠ 0) : DeficiencyTrivialAt (polyGaussCore (d := d)) (mixOp c b b') z
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteCarleman.mixOp_deficiencyTrivialAt`.

-- Generated from ChapterHermiteCarlemanEsa.lean — theorem BookProof.HermiteCarleman.mixOp_deficiencyTrivialAt
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterHermiteCarlemanEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.HermiteProductBasis
open BookProof.HermiteProductCore
open BookProof.HyperbolicQuadratic
open BookProof.HermiteCarleman



open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.HermiteRelative
open BookProof.QuadratureEsa
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {u : (Fin d →₀ ℕ) → ℂ} {lam : (Fin d →₀ ℕ) → ℝ} {amp : Fin d → ℂ} {z : ℂ}

theorem BookProof.HermiteCarleman.mixOp_deficiencyTrivialAt (c b b' : Fin d → ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (polyGaussCore (d := d)) (mixOp c b b') z := by sorry
