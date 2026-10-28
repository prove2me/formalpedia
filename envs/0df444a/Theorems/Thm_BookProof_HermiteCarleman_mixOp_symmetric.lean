-- Prove2me | Theorems.Thm_BookProof_HermiteCarleman_mixOp_symmetric
-- name    : BookProof.HermiteCarleman.mixOp_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:26:29.964491+00:00
-- url     : https://prove2.me/theorems/253ec068-779e-4c06-b4cb-215fc2d30960
-- title:
--   `BookProof.HermiteCarleman.mixOp_symmetric` (c b b' : Fin d → ℝ) : SymmetricOn (polyGaussCore (d := d)) (mixOp c b b')
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteCarlemanEsa`.
--
--   `BookProof.HermiteCarleman.mixOp_symmetric` (c b b' : Fin d → ℝ) : SymmetricOn (polyGaussCore (d := d)) (mixOp c b b')
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteCarleman.mixOp_symmetric`.

-- Generated from ChapterHermiteCarlemanEsa.lean — theorem BookProof.HermiteCarleman.mixOp_symmetric
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterHermiteCarlemanEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.HermiteProductCore
open BookProof.HermiteRelative
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

theorem BookProof.HermiteCarleman.mixOp_symmetric (c b b' : Fin d → ℝ) :
    SymmetricOn (polyGaussCore (d := d)) (mixOp c b b') := by sorry
