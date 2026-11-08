-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_mem_sBd
-- name    : BookProof.CarlemanSimplex.mem_sBd
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-07T22:45:37.724291+00:00
-- url     : https://prove2.me/theorems/3cfca215-0908-4d47-8054-6069ab036a30
-- title:
--   `BookProof.CarlemanSimplex.mem_sBd` {d N k : ℕ} {a : Fin d →₀ ℕ} : a ∈ sBd d N k ↔ deg a ≤ N ∧ N < deg a + k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.mem_sBd` {d N k : ℕ} {a : Fin d →₀ ℕ} : a ∈ sBd d N k ↔ deg a ≤ N ∧ N < deg a + k
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.mem_sBd`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.mem_sBd
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

theorem BookProof.CarlemanSimplex.mem_sBd {d N k : ℕ} {a : Fin d →₀ ℕ} :
    a ∈ sBd d N k ↔ deg a ≤ N ∧ N < deg a + k := by sorry
