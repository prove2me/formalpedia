-- Prove2me | Theorems.Thm_BookProof_HermiteCarleman_sum_shift
-- name    : BookProof.HermiteCarleman.sum_shift
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:21:31.726703+00:00
-- url     : https://prove2.me/theorems/a4c2aab2-c657-452a-998c-b6d460e15f7c
-- title:
--   `BookProof.HermiteCarleman.sum_shift` (d N : ℕ) (i : Fin d) (F : (Fin d →₀ ℕ) → ℂ) (hF : ∀ a : Fin d →₀ ℕ, a i = 0 → F a = 0) : ∑ a ∈ cube d N, F a = ∑ b ∈ inn d N...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteCarlemanEsa`.
--
--   `BookProof.HermiteCarleman.sum_shift` (d N : ℕ) (i : Fin d) (F : (Fin d →₀ ℕ) → ℂ) (hF : ∀ a : Fin d →₀ ℕ, a i = 0 → F a = 0) : ∑ a ∈ cube d N, F a = ∑ b ∈ inn d N i, F (b + Finsupp.single i 1)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteCarleman.sum_shift`.

-- Generated from ChapterHermiteCarlemanEsa.lean — theorem BookProof.HermiteCarleman.sum_shift
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

theorem BookProof.HermiteCarleman.sum_shift (d N : ℕ) (i : Fin d) (F : (Fin d →₀ ℕ) → ℂ)
    (hF : ∀ a : Fin d →₀ ℕ, a i = 0 → F a = 0) :
    ∑ a ∈ cube d N, F a = ∑ b ∈ inn d N i, F (b + Finsupp.single i 1) := by sorry
