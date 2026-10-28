-- Prove2me | Theorems.Thm_BookProof_HermiteCarleman_sum_lterm
-- name    : BookProof.HermiteCarleman.sum_lterm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:22:29.220269+00:00
-- url     : https://prove2.me/theorems/7d338694-5d3f-4a05-9ead-e3f3a15704e0
-- title:
--   `BookProof.HermiteCarleman.sum_lterm` (N : ℕ) (i : Fin d) : ∑ a ∈ cube d N, lterm u amp i a = (starRingEnd ℂ) (∑ a ∈ inn d N i, rterm u amp i a)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteCarlemanEsa`.
--
--   `BookProof.HermiteCarleman.sum_lterm` (N : ℕ) (i : Fin d) : ∑ a ∈ cube d N, lterm u amp i a = (starRingEnd ℂ) (∑ a ∈ inn d N i, rterm u amp i a)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteCarleman.sum_lterm`.

-- Generated from ChapterHermiteCarlemanEsa.lean — theorem BookProof.HermiteCarleman.sum_lterm
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

variable {u : (Fin d →₀ ℕ) → ℂ} {lam : (Fin d →₀ ℕ) → ℝ} {amp : Fin d → ℂ} {z : ℂ}

theorem BookProof.HermiteCarleman.sum_lterm (N : ℕ) (i : Fin d) :
    ∑ a ∈ cube d N, lterm u amp i a
      = (starRingEnd ℂ) (∑ a ∈ inn d N i, rterm u amp i a) := by sorry
