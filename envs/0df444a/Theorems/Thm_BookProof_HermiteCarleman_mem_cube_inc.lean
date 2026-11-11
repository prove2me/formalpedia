-- Prove2me | Theorems.Thm_BookProof_HermiteCarleman_mem_cube_inc
-- name    : BookProof.HermiteCarleman.mem_cube_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-10T17:43:38.148801+00:00
-- url     : https://prove2.me/theorems/84406ab7-2da5-4419-8a7b-bb7cc17fcd73
-- title:
--   `BookProof.HermiteCarleman.mem_cube_inc` {d N : ℕ} {a : Fin d →₀ ℕ} : a ∈ cube d N ↔ ∀ i, a i ≤ N
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteCarlemanEsa`.
--
--   `BookProof.HermiteCarleman.mem_cube_inc` {d N : ℕ} {a : Fin d →₀ ℕ} : a ∈ cube d N ↔ ∀ i, a i ≤ N
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteCarleman.mem_cube_inc`.
--
--   Same statement as `BookProof.HermiteCarleman.mem_cube`, republished with the smallest preamble that elaborates it (Mathlib + the chapter's Promoted bundle). The original node's preamble makes consumers fail on the platform with an empty environment, so it cannot be used as a dependency; see PIPELINE_PLAN §8.2.

-- Generated from ChapterHermiteCarlemanEsa.lean — theorem BookProof.HermiteCarleman.mem_cube_inc
--
-- REPLACEMENT node for `BookProof.HermiteCarleman.mem_cube`, whose preamble pulls
-- in `Def_ChapterHermiteProductCore` and eight more bundles.  Consumers that
-- import that node get an empty environment on the platform (every `open`
-- fails, `Finset` included) while the same file compiles locally, so the node
-- is unusable as a dependency.  This twin carries the SAME statement with the
-- smallest preamble that elaborates it: Mathlib plus the chapter's Promoted
-- bundle, which is where `cube` lives.  See PIPELINE_PLAN §8.2.
import Mathlib
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteCarleman.mem_cube_inc {d N : ℕ} {a : Fin d →₀ ℕ} :
    a ∈ cube d N ↔ ∀ i, a i ≤ N := by sorry
