-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_mem_sInn
-- name    : BookProof.CarlemanSimplex.mem_sInn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:46:08.430133+00:00
-- url     : https://prove2.me/theorems/512539b3-366c-48b2-ba1c-d2b580739a3e
-- title:
--   `BookProof.CarlemanSimplex.mem_sInn` {d N k : ℕ} {a : Fin d →₀ ℕ} : a ∈ sInn d N k ↔ deg a + k ≤ N
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.mem_sInn` {d N k : ℕ} {a : Fin d →₀ ℕ} : a ∈ sInn d N k ↔ deg a + k ≤ N
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.mem_sInn`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.mem_sInn
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Mathlib
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.CarlemanSimplex



open Finset
open BookProof.HermiteCarleman BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

theorem BookProof.CarlemanSimplex.mem_sInn {d N k : ℕ} {a : Fin d →₀ ℕ} : a ∈ sInn d N k ↔ deg a + k ≤ N := by sorry
