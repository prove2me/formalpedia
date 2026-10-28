-- Prove2me | Theorems.Thm_BookProof_HermiteCarleman_sum_cube_split
-- name    : BookProof.HermiteCarleman.sum_cube_split
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:21:51.546221+00:00
-- url     : https://prove2.me/theorems/a14945d1-095b-46be-9365-1f1ea3aa6e4e
-- title:
--   `BookProof.HermiteCarleman.sum_cube_split` (d N : ℕ) (i : Fin d) (F : (Fin d →₀ ℕ) → ℂ) : ∑ a ∈ cube d N, F a = ∑ a ∈ inn d N i, F a + ∑ a ∈ face d N i, F a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteCarlemanEsa`.
--
--   `BookProof.HermiteCarleman.sum_cube_split` (d N : ℕ) (i : Fin d) (F : (Fin d →₀ ℕ) → ℂ) : ∑ a ∈ cube d N, F a = ∑ a ∈ inn d N i, F a + ∑ a ∈ face d N i, F a
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteCarleman.sum_cube_split`.

-- Generated from ChapterHermiteCarlemanEsa.lean — theorem BookProof.HermiteCarleman.sum_cube_split
import Definitions.Def_ChapterHermiteProductCore
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
import Definitions.Def_ChapterGaussCoreQuadBounds
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

theorem BookProof.HermiteCarleman.sum_cube_split (d N : ℕ) (i : Fin d) (F : (Fin d →₀ ℕ) → ℂ) :
    ∑ a ∈ cube d N, F a = ∑ a ∈ inn d N i, F a + ∑ a ∈ face d N i, F a := by sorry
