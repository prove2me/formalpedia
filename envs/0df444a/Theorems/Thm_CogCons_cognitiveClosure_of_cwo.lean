-- Prove2me | Theorems.Thm_CogCons_cognitiveClosure_of_cwo
-- name    : CogCons.cognitiveClosure_of_cwo
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T18:28:09.681364+00:00
-- url     : https://prove2.me/theorems/42aa8b37-ae75-4d44-94fd-bbdb81aa0b25
-- title:
--   Corollary 3.5: cognitive closure of a CWO set and its complement
-- statement:
--   If $A \in \tau$, then
--   $$\mathrm{Cl}^{\square}(A) \neq A \quad\text{and}\quad \mathrm{Cl}^{\square}(C \setminus A) = C \setminus A.$$
-- source:
--   S. Acharjee and U. Gogoi, *The limit of human intelligence*, arXiv:2310.10792v2 [math.GM] (2023), https://arxiv.org/abs/2310.10792, Corollary 3.5 (p. 8)

import Mathlib
import Definitions.Def_CogCons_consequence_space

open CogCons.CognitiveConsequenceSpace

namespace CogCons

theorem cognitiveClosure_of_cwo {C : Type*} (S : CognitiveConsequenceSpace C) (A : Set C)
    (hA : S.IsCWO A) :
    S.cognitiveClosure A ≠ A ∧ S.cognitiveClosure Aᶜ = Aᶜ := by sorry

end CogCons
