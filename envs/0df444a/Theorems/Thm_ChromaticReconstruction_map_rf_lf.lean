-- Prove2me | Theorems.Thm_ChromaticReconstruction_map_rf_lf
-- name    : ChromaticReconstruction.map_rf_lf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T15:09:14.578932+00:00
-- url     : https://prove2.me/theorems/8101cb8b-7cb7-4a53-969d-0c0e38537f56
-- title:
--   Chromatic Reconstruction: map rf lf
-- statement:
--   The Chromatic Reconstruction construction uses the map rf lf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean#L225-L230
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean#L225-L230

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

theorem ChromaticReconstruction.map_rf_lf {s : ℕ} (hn : 2 * c + 3 ≤ n) (hp : p = c ∨ p = c + 1) (hs1 : 1 ≤ s)
    (hs2 : s ≤ c + 1) : Sym2.map (rf n c s) (lf n p) = lf n (2 * c + 1 - p) := by sorry
