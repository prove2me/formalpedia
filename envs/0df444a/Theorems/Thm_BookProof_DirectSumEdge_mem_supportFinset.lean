-- Prove2me | Theorems.Thm_BookProof_DirectSumEdge_mem_supportFinset
-- name    : BookProof.DirectSumEdge.mem_supportFinset
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:57:00.430071+00:00
-- url     : https://prove2.me/theorems/61c71275-575d-4b09-a118-fed689a36c2f
-- title:
--   `BookProof.DirectSumEdge.mem_supportFinset` {x : dsCore D} {i : ι} : i ∈ supportFinset x ↔ ((x : lp G 2) : ∀ i, G i) i ≠ 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDirectSumEdge`.
--
--   `BookProof.DirectSumEdge.mem_supportFinset` {x : dsCore D} {i : ι} : i ∈ supportFinset x ↔ ((x : lp G 2) : ∀ i, G i) i ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.DirectSumEdge.mem_supportFinset`.

-- Generated from ChapterDirectSumEdge.lean — theorem BookProof.DirectSumEdge.mem_supportFinset
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterDirectSumEdge
import Definitions.Def_ChapterDirectSumEsa
open BookProof.DirectSumEsa
open BookProof.DirectSumEdge



open BookProof.FarisLavine BookProof.DirectSumEsa

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] {D : ∀ i, Submodule ℂ (G i)}

theorem BookProof.DirectSumEdge.mem_supportFinset {x : dsCore D} {i : ι} :
    i ∈ supportFinset x ↔ ((x : lp G 2) : ∀ i, G i) i ≠ 0 := by sorry
