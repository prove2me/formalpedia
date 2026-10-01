-- Prove2me | Theorems.Thm_CogCons_cwo_iUnion
-- name    : CogCons.cwo_iUnion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T17:08:58.769465+00:00
-- url     : https://prove2.me/theorems/e3e9eb70-06dd-4376-87d9-8b968c075202
-- title:
--   Theorem 3.1: arbitrary unions of CWO sets are CWO
-- statement:
--   Let $(C, \mathrm{Cn})$ be a cognitive-consequence space and $(A_i)_{i \in \Delta}$ an arbitrary family of CWO sets. Then
--   $$\bigcup_{i \in \Delta} A_i \in \tau.$$
--
--   This makes $\tau$ closed under arbitrary unions.
-- source:
--   S. Acharjee and U. Gogoi, *The limit of human intelligence*, arXiv:2310.10792v2 [math.GM] (2023), https://arxiv.org/abs/2310.10792, Theorem 3.1 (p. 5)

import Mathlib
import Definitions.Def_CogCons_consequence_space

open CogCons.CognitiveConsequenceSpace

namespace CogCons

theorem cwo_iUnion {C : Type*} (S : CognitiveConsequenceSpace C) {ι : Type*}
    (A : ι → Set C) (hA : ∀ i, S.IsCWO (A i)) :
    S.IsCWO (⋃ i, A i) := by sorry

end CogCons
