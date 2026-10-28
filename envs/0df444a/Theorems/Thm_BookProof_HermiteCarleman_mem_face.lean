-- Prove2me | Theorems.Thm_BookProof_HermiteCarleman_mem_face
-- name    : BookProof.HermiteCarleman.mem_face
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:20:54.93208+00:00
-- url     : https://prove2.me/theorems/953403e8-3d1b-4a41-ae79-3bc341ce3785
-- title:
--   `BookProof.HermiteCarleman.mem_face` {d N : ℕ} {i : Fin d} {a : Fin d →₀ ℕ} : a ∈ face d N i ↔ (∀ j, a j ≤ N) ∧ a i = N
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteCarlemanEsa`.
--
--   `BookProof.HermiteCarleman.mem_face` {d N : ℕ} {i : Fin d} {a : Fin d →₀ ℕ} : a ∈ face d N i ↔ (∀ j, a j ≤ N) ∧ a i = N
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteCarleman.mem_face`.

-- Generated from ChapterHermiteCarlemanEsa.lean — theorem BookProof.HermiteCarleman.mem_face
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

theorem BookProof.HermiteCarleman.mem_face {d N : ℕ} {i : Fin d} {a : Fin d →₀ ℕ} :
    a ∈ face d N i ↔ (∀ j, a j ≤ N) ∧ a i = N := by sorry
