-- Prove2me | Theorems.Thm_BookProof_HermiteCarleman_not_summable_inv_sqrt
-- name    : BookProof.HermiteCarleman.not_summable_inv_sqrt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:24:44.958872+00:00
-- url     : https://prove2.me/theorems/6746e43d-a9c6-49b6-9eae-01456374bc3c
-- title:
--   `BookProof.HermiteCarleman.not_summable_inv_sqrt` : ¬ Summable (fun N : ℕ => (Real.sqrt ((N : ℝ) + 1))⁻¹)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteCarlemanEsa`.
--
--   `BookProof.HermiteCarleman.not_summable_inv_sqrt` : ¬ Summable (fun N : ℕ => (Real.sqrt ((N : ℝ) + 1))⁻¹)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteCarleman.not_summable_inv_sqrt`.

-- Generated from ChapterHermiteCarlemanEsa.lean — theorem BookProof.HermiteCarleman.not_summable_inv_sqrt
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

theorem BookProof.HermiteCarleman.not_summable_inv_sqrt : ¬ Summable (fun N : ℕ => (Real.sqrt ((N : ℝ) + 1))⁻¹) := by sorry
