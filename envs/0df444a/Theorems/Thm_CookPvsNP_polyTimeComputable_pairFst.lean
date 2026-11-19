-- Prove2me | Theorems.Thm_CookPvsNP_polyTimeComputable_pairFst
-- name    : CookPvsNP.polyTimeComputable_pairFst
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-18T20:08:07.297206+00:00
-- url     : https://prove2.me/theorems/cfb944ec-587b-4744-9ece-4e0b439c0c19
-- title:
--   The first projection of the pair code is polynomial-time computable
-- statement:
--   For finite alphabets $A$ and $B$, a pair of words $(w,y)$ is coded as $w\#y$ over $\{\#\}\cup(A\sqcup B)$, with $\#$ the separator as in Cook's checking languages. Some polynomial-time computable $g$ satisfies
--   $$g(w\#y)=w\qquad\text{for all words } w\in A^*,\ y\in B^*.$$
--
--   This is the companion of the proved second projection lemma. It lets a search-reduction decoder recover the original instance from the instance–answer pair.
--
--   **Formalization Note** $g$ is total and must run in polynomial time on all words; its values on words not of the form $w\#y$ are unconstrained.
-- source:
--   S. Cook, The P versus NP problem (Clay Mathematics Institute), Section 1, checking relations and the language L_R = {w#y}; companion of CookPvsNP.polyTimeComputable_pairSnd

import Definitions.Def_CookPvsNP_defs

namespace CookPvsNP

theorem polyTimeComputable_pairFst (A B : Type) [Fintype A] [Fintype B] :
    ∃ g : List (Option (A ⊕ B)) → List A, PolyTimeComputable g ∧
      ∀ (s : List A) (t : List B),
        g (s.map (some ∘ Sum.inl) ++ none :: t.map (some ∘ Sum.inr)) = s := by sorry

end CookPvsNP
