-- Prove2me | Theorems.Thm_CogCons_deductiveFilter_isFilter
-- name    : CogCons.deductiveFilter_isFilter
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T18:38:59.020059+00:00
-- url     : https://prove2.me/theorems/5b17a27c-3b8a-4e53-908b-acc6244254ec
-- title:
--   Theorem 4.3: the family f_d is a filter on the deductive part
-- statement:
--   Let $C_d \subsetneq C$ be a deductive system (the deductive part of $C$) and $f \in C_d$. Let $f_d$ be the family of subsets $A \subseteq C_d$ with $f \in A$ that contain a deductive subset. Then:
--
--   1. $C_d \in f_d$;
--   2. if $A \in f_d$ and $A \subseteq B \subseteq C_d$, then $B \in f_d$;
--   3. if $A, B \in f_d$, then $A \cap B \in f_d$.
--
--   So $f_d$ is a filter on $C_d$.
-- source:
--   S. Acharjee and U. Gogoi, *The limit of human intelligence*, arXiv:2310.10792v2 [math.GM] (2023), https://arxiv.org/abs/2310.10792, Theorem 4.3 (p. 18)

import Mathlib
import Definitions.Def_CogCons_consequence_space

open CogCons.CognitiveConsequenceSpace

namespace CogCons

theorem deductiveFilter_isFilter {C : Type*} (S : CognitiveConsequenceSpace C)
    (Cd : Set C) (hCd : S.IsDeductive Cd) (hCd_ne : Cd ≠ Set.univ) (f : C) (hf : f ∈ Cd) :
    Cd ∈ S.deductiveFilter Cd f ∧
    (∀ A B : Set C, A ∈ S.deductiveFilter Cd f → A ⊆ B → B ⊆ Cd →
      B ∈ S.deductiveFilter Cd f) ∧
    (∀ A B : Set C, A ∈ S.deductiveFilter Cd f → B ∈ S.deductiveFilter Cd f →
      A ∩ B ∈ S.deductiveFilter Cd f) := by sorry

end CogCons
