-- Prove2me | Theorems.Thm_BookProof_DirectSumEdge_coe_eq_zero_of_notMem_supportFinset
-- name    : BookProof.DirectSumEdge.coe_eq_zero_of_notMem_supportFinset
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:57:05.4844+00:00
-- url     : https://prove2.me/theorems/856a9929-852c-4972-8c1e-42f448a22071
-- title:
--   `BookProof.DirectSumEdge.coe_eq_zero_of_notMem_supportFinset` {x : dsCore D} {i : ι} (hi : i ∉ supportFinset x) : ((x : lp G 2) : ∀ i, G i) i = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDirectSumEdge`.
--
--   `BookProof.DirectSumEdge.coe_eq_zero_of_notMem_supportFinset` {x : dsCore D} {i : ι} (hi : i ∉ supportFinset x) : ((x : lp G 2) : ∀ i, G i) i = 0
--
--   Formalization note: Lean 4 identifier `BookProof.DirectSumEdge.coe_eq_zero_of_notMem_supportFinset`.

-- Generated from ChapterDirectSumEdge.lean — theorem BookProof.DirectSumEdge.coe_eq_zero_of_notMem_supportFinset
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

theorem BookProof.DirectSumEdge.coe_eq_zero_of_notMem_supportFinset {x : dsCore D} {i : ι}
    (hi : i ∉ supportFinset x) : ((x : lp G 2) : ∀ i, G i) i = 0 := by sorry
