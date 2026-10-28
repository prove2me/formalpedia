-- Prove2me | Theorems.Thm_BookProof_HermiteCarleman_lterm_shift
-- name    : BookProof.HermiteCarleman.lterm_shift
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:22:53.518985+00:00
-- url     : https://prove2.me/theorems/8f379a0a-3b82-4f10-8e4c-fc6cfc2cec41
-- title:
--   `BookProof.HermiteCarleman.lterm_shift` (i : Fin d) (b : Fin d →₀ ℕ) : lterm u amp i (b + Finsupp.single i 1) = (starRingEnd ℂ) (rterm u amp i b)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteCarlemanEsa`.
--
--   `BookProof.HermiteCarleman.lterm_shift` (i : Fin d) (b : Fin d →₀ ℕ) : lterm u amp i (b + Finsupp.single i 1) = (starRingEnd ℂ) (rterm u amp i b)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteCarleman.lterm_shift`.

-- Generated from ChapterHermiteCarlemanEsa.lean — theorem BookProof.HermiteCarleman.lterm_shift
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

theorem BookProof.HermiteCarleman.lterm_shift (i : Fin d) (b : Fin d →₀ ℕ) :
    lterm u amp i (b + Finsupp.single i 1) = (starRingEnd ℂ) (rterm u amp i b) := by sorry
