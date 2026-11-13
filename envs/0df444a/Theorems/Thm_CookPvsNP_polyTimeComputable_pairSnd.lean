-- Prove2me | Theorems.Thm_CookPvsNP_polyTimeComputable_pairSnd
-- name    : CookPvsNP.polyTimeComputable_pairSnd
-- status  : Proved
-- author  : @utkuokur
-- created : 2026-11-12T19:53:58.84298+00:00
-- url     : https://prove2.me/theorems/cfae154b-51cb-47d9-81cc-f8b239f39700
-- title:
--   Reading the second component of a coded pair $w\#y$ is polynomial-time computable
-- statement:
--   Let $A$ and $B$ be finite alphabets. A pair of words $(w,y)\in A^*\times B^*$ is coded as the single word $w\#y$ over the alphabet $A\sqcup B\sqcup\{\#\}$: the letters of $w$, then the separator $\#$, then the letters of $y$.
--
--   The lemma states that the second component can be read off in polynomial time: there is a function $g$ from words over $A\sqcup B\sqcup\{\#\}$ to words over $B$, computable in polynomial time by a deterministic one-tape Turing machine, such that
--
--   $$
--   g(w\#y)\;=\;y\qquad\text{for all } w\in A^*,\ y\in B^* .
--   $$
--
--   A polynomial-time search reduction consists of an instance map and a decoder, and the decoder receives the coded pair of the source instance and an answer to the target instance. When the reduction leaves answers unchanged, the decoder is exactly this projection. This is the case in Theorem C.3 of Xiong and Vlatakis-Gkaragkounis, where every answer of type (HO1), (HO2) or (HO3) is itself an answer of type (CO1), (CO2) or (CO3). The lemma is independent of any particular search problem and can be reused by other reductions stated with the pair code.
--
--   Differences from the source:
--   - auxiliary statement: the paper only asserts that solutions "can be decoded in polynomial time" (p.37) and defines reductions with "a polynomial-time decoder that maps every valid solution of the target instance to a valid solution of the source instance" (p.7); it does not spell out the machine.
--
--   **Formalization Note** Polynomial-time computability is the public `CookPvsNP.PolyTimeComputable`: some machine halts on every input word $x$ within $|x|^k+k$ steps with the value on its tape. The pair alphabet is `Option (A ⊕ B)` with `none` as the separator, as in `CookPvsNP.checkLang` and `CardinalMatching.SearchReduces`. The function $g$ is total and must be polynomial-time on all words; its values on words that are not of the form $w\#y$ are not prescribed.
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101v4 (3 Nov 2026), https://arxiv.org/abs/2609.14101, Section 2, p.7 (polynomial-time many-one reductions with a polynomial-time decoder) and proof of Theorem C.3, p.37 (solutions are decoded unchanged). Machine model and pair code: the platform's public CookPvsNP definitions. Auxiliary lemma, not stated in the paper.

import Mathlib
import Definitions.Def_CookPvsNP_defs

set_option autoImplicit false

namespace CookPvsNP

/-- **The second projection of the pair code is polynomial-time computable.** For finite
alphabets `A` and `B`, a pair of words `(w, y)` is coded as `w#y` over `Option (A ⊕ B)`, where
`none` is the separator `#` (as in `checkLang`). Some polynomial-time computable `g` satisfies
`g (w#y) = y` for all words `w` and `y`.

This is the decoder of a search reduction that leaves answers unchanged, e.g. the reduction of
Xiong–Vlatakis-Gkaragkounis, arXiv:2609.14101v4, Theorem C.3 (p.37: "every solution of the
constructed … instance can be decoded in polynomial time into a solution of the original …
instance").

**Formalization Note** `g` is total and must be polynomial-time on all words; its values on words
that are not of the form `w#y` are not prescribed. -/
theorem polyTimeComputable_pairSnd (A B : Type) [Fintype A] [Fintype B] :
    ∃ g : List (Option (A ⊕ B)) → List B, PolyTimeComputable g ∧
      ∀ (s : List A) (t : List B),
        g (s.map (some ∘ Sum.inl) ++ none :: t.map (some ∘ Sum.inr)) = t := by sorry

end CookPvsNP
