-- Prove2me | Theorems.Thm_CogCons_exists_not_mem_cwo
-- name    : CogCons.exists_not_mem_cwo
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T17:34:09.984139+00:00
-- url     : https://prove2.me/theorems/4c3686c2-f8f9-464a-a0df-dc15cdb5bb1f
-- title:
--   Theorem 3.3: some thought lies in no CWO set
-- statement:
--   In every cognitive-consequence space there is a mental representation $f \in C$ that belongs to no CWO set:
--   $$\exists f \in C\ \ \forall A \in \tau:\ f \notin A.$$
-- source:
--   S. Acharjee and U. Gogoi, *The limit of human intelligence*, arXiv:2310.10792v2 [math.GM] (2023), https://arxiv.org/abs/2310.10792, Theorem 3.3 (p. 7)

import Mathlib
import Definitions.Def_CogCons_consequence_space

open CogCons.CognitiveConsequenceSpace

namespace CogCons

theorem exists_not_mem_cwo {C : Type*} (S : CognitiveConsequenceSpace C) :
    ∃ f : C, ∀ A : Set C, S.IsCWO A → f ∉ A := by sorry

end CogCons
