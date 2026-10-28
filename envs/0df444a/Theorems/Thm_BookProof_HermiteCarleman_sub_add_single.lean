-- Prove2me | Theorems.Thm_BookProof_HermiteCarleman_sub_add_single
-- name    : BookProof.HermiteCarleman.sub_add_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:21:04.272314+00:00
-- url     : https://prove2.me/theorems/54244253-75f8-4851-bf7d-6961c2b305a3
-- title:
--   `BookProof.HermiteCarleman.sub_add_single` {d : ℕ} {i : Fin d} {a : Fin d →₀ ℕ} (h : a i ≠ 0) : (a - Finsupp.single i 1) + Finsupp.single i 1 = a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteCarlemanEsa`.
--
--   `BookProof.HermiteCarleman.sub_add_single` {d : ℕ} {i : Fin d} {a : Fin d →₀ ℕ} (h : a i ≠ 0) : (a - Finsupp.single i 1) + Finsupp.single i 1 = a
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteCarleman.sub_add_single`.

-- Generated from ChapterHermiteCarlemanEsa.lean — theorem BookProof.HermiteCarleman.sub_add_single
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

theorem BookProof.HermiteCarleman.sub_add_single {d : ℕ} {i : Fin d} {a : Fin d →₀ ℕ} (h : a i ≠ 0) :
    (a - Finsupp.single i 1) + Finsupp.single i 1 = a := by sorry
