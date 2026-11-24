-- Prove2me | Theorems.Thm_ChromaticReconstruction_opD_pre
-- name    : ChromaticReconstruction.opD_pre
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T12:32:42.965255+00:00
-- url     : https://prove2.me/theorems/c865d355-e3fd-4069-babb-297d38e9b613
-- title:
--   Chromatic Reconstruction: op D pre
-- statement:
--   The Chromatic Reconstruction construction uses the op D pre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Uniform.lean#L81-L98
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Uniform.lean#L81-L98

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Uniform
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]

theorem ChromaticReconstruction.opD_pre (q N : ℕ) (G : SimpleGraph V) (hN : Fintype.card V < N) :
    ∑ r ∈ range N, C (r : ℚ) * X (q * r - 1) * psiQ q (pderiv r (chromSymm G)) =
      ∑ F ∈ G.edgeFinset.powerset, C ((-1) ^ F.card) * ∑ C0 ∈ compSets (F : Set (Sym2 V)),
        C (C0.card : ℚ) * (X (q * C0.card - 1) *
          ∏ C ∈ (compSets (F : Set (Sym2 V))).erase C0, X (q * C.card)) := by sorry
