-- Prove2me | Theorems.Thm_BraidsLinksMCG_hurwitz_local_cancellation
-- name    : BraidsLinksMCG.hurwitz_local_cancellation
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T00:07:24.013397+00:00
-- url     : https://prove2.me/theorems/83eeb633-aec5-474b-85f1-7696c73559d9
-- title:
--   Local Hurwitz cancellation in a free group
-- statement:
--   A purely free-group cancellation statement; no braid group appears.
--
--   Let $w_1,\dots,w_n$ be elements of the free group $F_n = \langle x_1,\dots,x_n\rangle$, each a conjugate of a generator,
--   $$w_i = A_i\, x_{\mu(i)}\, A_i^{-1} \qquad (\mu \text{ a permutation of } \{1,\dots,n\}),$$
--   whose product in order is the whole word:
--   $$w_1 w_2 \cdots w_n = x_1 x_2 \cdots x_n .$$
--   Assume the tuple is not already the trivial one up to relabelling, i.e. it is not the case that every $w_i$ is itself a generator. Then some adjacent pair $(a, a+1)$ admits a length-decreasing conjugation: either
--   $$\lVert w_a w_{a+1} w_a^{-1}\rVert < \lVert w_{a+1}\rVert \qquad\text{or}\qquad \lVert w_{a+1}^{-1} w_a w_{a+1}\rVert < \lVert w_a\rVert,$$
--   the norm being the length of the reduced word.
--
--   **What this is.** These are exactly the two Hurwitz moves at position $a$,
--   $$(\dots, w_a, w_{a+1},\dots) \;\longmapsto\; (\dots, w_aw_{a+1}w_a^{-1},\, w_a,\dots) \quad\text{and}\quad (\dots,w_{a+1},\, w_{a+1}^{-1}w_aw_{a+1},\dots),$$
--   each of which preserves both the ordered product and the property of being a tuple of conjugates of generators. The claim is that as long as the tuple is not the base tuple $(x_{\nu(1)},\dots,x_{\nu(n)})$, one of the $2(n-1)$ moves strictly decreases $\sum_i \lVert w_i\rVert$. Since one move changes only two entries, and the entry $w_a$ merely shifts position in the first case and $w_{a+1}$ in the second, the change in the total is exactly the difference displayed above.
--
--   **Why it is plausible and where the content lies.** Normalise each $A_i$ so that $A_i x_{\mu(i)} A_i^{-1}$ is reduced as written; then $\lVert w_i\rVert = 2\lvert A_i\rvert + 1$ and the total is $n + 2\sum_i \lvert A_i\rvert$, while the product has length exactly $n$. So the amount of cancellation occurring in $w_1\cdots w_n$ is forced to be as large as it can be, and the whole difficulty is to convert that global cancellation into a statement about one adjacent pair. The hypothesis that not every $w_i$ is a generator says precisely that some $A_i$ is non-trivial, i.e. that the total exceeds its minimum value $n$.
--
--   The statement is the combinatorial heart of Artin's characterization of the braid automorphisms of a free group, isolated from the braid group: it is what makes the descent in `BraidsLinksMCG.artin_hurwitz_norm_reduction` terminate, and through that it is the last non-topological obstruction in this mission. It involves no presented group, no group action, and no topology --- only reduced words in a free group.
--
--   Note that the conclusion is genuinely a disjunction over both directions of the move. The first alternative alone is false: a tuple can be at a local minimum for all positive moves while a negative move still shortens it.
-- source:
--   Artin, Theory of braids, Ann. of Math. 48 (1947), Section 1; Birman, Braids, Links and Mapping Class Groups, Theorem 1.9; Kassel-Turaev, Braid Groups, Theorem 1.17 and the Hurwitz action of B_n on tuples of conjugates of the generators.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

namespace BraidsLinksMCG

theorem hurwitz_local_cancellation (n : ℕ)
    (w : Fin n → FreeGroup (Fin n))
    (mu : Equiv.Perm (Fin n)) (A : Fin n → FreeGroup (Fin n))
    (hw : ∀ i : Fin n, w i = A i * FreeGroup.of (mu i) * (A i)⁻¹)
    (hprod : (List.ofFn w).prod = freeWordProd n)
    (hnotperm : ¬ ∃ nu : Equiv.Perm (Fin n), ∀ i : Fin n, w i = FreeGroup.of (nu i)) :
    ∃ a b : Fin n, (b : ℕ) = (a : ℕ) + 1 ∧
      (FreeGroup.norm (w a * w b * (w a)⁻¹) < FreeGroup.norm (w b) ∨
        FreeGroup.norm ((w b)⁻¹ * w a * w b) < FreeGroup.norm (w a)) := by sorry

end BraidsLinksMCG
