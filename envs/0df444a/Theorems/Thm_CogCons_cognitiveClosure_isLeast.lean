-- Prove2me | Theorems.Thm_CogCons_cognitiveClosure_isLeast
-- name    : CogCons.cognitiveClosure_isLeast
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T17:53:19.996636+00:00
-- url     : https://prove2.me/theorems/e26b1557-6590-4977-8501-bd2ee1bdc892
-- title:
--   Theorem 3.6: cognitive closure is the least deductive superset
-- statement:
--   For every $A \subseteq C$, the cognitive closure $\mathrm{Cl}^{\square}(A)$ is the smallest deductive system containing $A$: it is deductive, contains $A$, and is contained in every deductive system containing $A$.
-- source:
--   S. Acharjee and U. Gogoi, *The limit of human intelligence*, arXiv:2310.10792v2 [math.GM] (2023), https://arxiv.org/abs/2310.10792, Theorem 3.6 (pp. 7–8)

import Mathlib
import Definitions.Def_CogCons_consequence_space

open CogCons.CognitiveConsequenceSpace

namespace CogCons

theorem cognitiveClosure_isLeast {C : Type*} (S : CognitiveConsequenceSpace C) (A : Set C) :
    IsLeast {D : Set C | S.IsDeductive D ∧ A ⊆ D} (S.cognitiveClosure A) := by sorry

end CogCons
