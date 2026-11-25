-- Prove2me | Theorems.Thm_ChromaticReconstruction_not_mem_of_far
-- name    : ChromaticReconstruction.not_mem_of_far
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T15:06:24.074522+00:00
-- url     : https://prove2.me/theorems/9727503d-852f-421a-be72-6808aa199a67
-- title:
--   Chromatic Reconstruction: not mem of far
-- statement:
--   The Chromatic Reconstruction construction uses the not mem of far property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean#L142-L146
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean#L142-L146

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}
variable {p : ℕ} {F : Finset (Sym2 (Fin (n + 1)))}

theorem ChromaticReconstruction.not_mem_of_far {a b : ℕ} (hF : F ⊆ (PL n p).edgeFinset) (ha : a ≤ n) (hb : b ≤ n)
    (h1 : a + 1 ≠ b) (h2 : b + 1 ≠ a) (h3 : a ≠ n) (h4 : b ≠ n) : s(vx n a, vx n b) ∉ F := by sorry
