-- Prove2me | Theorems.Thm_ChromaticReconstruction_psiMap_spec
-- name    : ChromaticReconstruction.psiMap_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T15:21:28.317241+00:00
-- url     : https://prove2.me/theorems/443c50ba-0feb-4513-86b2-820d2d1c5ae1
-- title:
--   Chromatic Reconstruction: psi Map spec
-- statement:
--   The Chromatic Reconstruction construction uses the psi Map spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean#L284-L380
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean#L284-L380

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}

theorem ChromaticReconstruction.psiMap_spec {p : ℕ} {F : Finset (Sym2 (Fin (n + 1)))} (hn : 2 * c + 3 ≤ n)
    (hp : p = c ∨ p = c + 1) (hF : F ⊆ (PL n p).edgeFinset) (hcard : F.card ≤ c + 1) :
    psiMap n c p F ⊆ (PL n (2 * c + 1 - p)).edgeFinset ∧
      compType (psiMap n c p F : Set (Sym2 (Fin (n + 1)))) =
        compType (F : Set (Sym2 (Fin (n + 1)))) ∧
      psiMap n c (2 * c + 1 - p) (psiMap n c p F) = F := by sorry
