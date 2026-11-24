-- Prove2me | Theorems.Thm_ChromaticReconstruction_lf_not_mem
-- name    : ChromaticReconstruction.lf_not_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T15:16:28.742593+00:00
-- url     : https://prove2.me/theorems/b4f37b96-67dd-4540-8562-4ba96d87146d
-- title:
--   Chromatic Reconstruction: lf not mem
-- statement:
--   The Chromatic Reconstruction construction uses the lf not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean#L232-L238
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean#L232-L238

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

theorem ChromaticReconstruction.lf_not_mem {q : ℕ} (hpn : p < n) (hqn : q < n) (hpq : p ≠ q)
    (hF : F ⊆ (PL n p).edgeFinset) : lf n q ∉ F := by sorry
