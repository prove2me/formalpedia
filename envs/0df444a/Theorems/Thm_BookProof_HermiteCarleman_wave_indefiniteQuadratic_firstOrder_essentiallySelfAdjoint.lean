-- Prove2me | Theorems.Thm_BookProof_HermiteCarleman_wave_indefiniteQuadratic_firstOrder_essentiallySelfAdjoint
-- name    : BookProof.HermiteCarleman.wave_indefiniteQuadratic_firstOrder_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:26:47.790266+00:00
-- url     : https://prove2.me/theorems/c1403a62-a74b-4799-91cc-39d3d7a4b272
-- title:
--   `BookProof.HermiteCarleman.wave_indefiniteQuadratic_firstOrder_essentiallySelfAdjoint` (n : ℕ) (b b' : Fin (1 + n) → ℝ) : EssentiallySelfAdjointOn (polyGaussCore (d := 1 + n)) (mix
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteCarlemanEsa`.
--
--   `BookProof.HermiteCarleman.wave_indefiniteQuadratic_firstOrder_essentiallySelfAdjoint` (n : ℕ) (b b' : Fin (1 + n) → ℝ) : EssentiallySelfAdjointOn (polyGaussCore (d := 1 + n)) (mixOp (minkowskiCoeff n) b b')
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteCarleman.wave_indefiniteQuadratic_firstOrder_essentiallySelfAdjoint`.

-- Generated from ChapterHermiteCarlemanEsa.lean — theorem BookProof.HermiteCarleman.wave_indefiniteQuadratic_firstOrder_essentiallySelfAdjoint
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterHermiteCarlemanEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterShiftedQuadraticEsa
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

theorem BookProof.HermiteCarleman.wave_indefiniteQuadratic_firstOrder_essentiallySelfAdjoint (n : ℕ)
    (b b' : Fin (1 + n) → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := 1 + n)) (mixOp (minkowskiCoeff n) b b') := by sorry
