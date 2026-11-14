-- Prove2me | Theorems.Thm_CookPvsNP_polyTimeComputable_tagged_pair
-- name    : CookPvsNP.polyTimeComputable_tagged_pair
-- status  : Open
-- author  : @Weiqiang
-- created : 2026-11-13T20:43:24.53272+00:00
-- url     : https://prove2.me/theorems/80c375f0-957d-480b-b06a-16eca99a5026
-- title:
--   Polynomial-time functions admit tagged pairing on a shared input
-- statement:
--   Let $f:A^*\to B^*$ and $g:A^*\to C^*$ be polynomial-time functions on words over finite alphabets. Write $u\#v$ for a tagged copy of $u$, a fresh separator, and a tagged copy of $v$. Then the function
--   $$x\longmapsto f(x)\#g(x)$$
--   is polynomial-time computable on a deterministic one-tape Turing machine. The same input supplies both computations. This closure property is used to implement the answer map in the composition of Levin reductions.
-- source:
--   Cook, The P versus NP Problem, Appendix (one-tape Turing machine model), https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf . Standard closure construction for the tagged pairing used in polynomial-time search reductions.

import Definitions.Def_CookPvsNP_defs

namespace CookPvsNP

theorem polyTimeComputable_tagged_pair {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (f : List A → List B) (g : List A → List C)
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => (f x).map (some ∘ Sum.inl) ++ none :: (g x).map (some ∘ Sum.inr)) := by sorry

end CookPvsNP
