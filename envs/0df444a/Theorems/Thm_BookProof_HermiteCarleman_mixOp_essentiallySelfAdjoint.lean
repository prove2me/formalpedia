-- Prove2me | Theorems.Thm_BookProof_HermiteCarleman_mixOp_essentiallySelfAdjoint
-- name    : BookProof.HermiteCarleman.mixOp_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:25:49.604265+00:00
-- url     : https://prove2.me/theorems/0637dea8-4256-4b7d-ad25-84637ce573a3
-- title:
--   `BookProof.HermiteCarleman.mixOp_essentiallySelfAdjoint` (c b b' : Fin d → ℝ) : EssentiallySelfAdjointOn (polyGaussCore (d := d)) (mixOp c b b')
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteCarlemanEsa`.
--
--   `BookProof.HermiteCarleman.mixOp_essentiallySelfAdjoint` (c b b' : Fin d → ℝ) : EssentiallySelfAdjointOn (polyGaussCore (d := d)) (mixOp c b b')
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteCarleman.mixOp_essentiallySelfAdjoint`.

-- Generated from ChapterHermiteCarlemanEsa.lean — theorem BookProof.HermiteCarleman.mixOp_essentiallySelfAdjoint
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterHermiteCarlemanEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.HermiteProductCore
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

theorem BookProof.HermiteCarleman.mixOp_essentiallySelfAdjoint (c b b' : Fin d → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (mixOp c b b') := by sorry
