-- Prove2me | Theorems.Thm_CountOrderings_NFree_lemma_6_2
-- name    : CountOrderings.NFree.lemma_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:58:11.447211+00:00
-- url     : https://prove2.me/theorems/a43eca22-6c48-4e60-90e3-f9bb47c8ead6
-- title:
--   Lemma 6.2 — every exact cover carries total weight $(4h)!/(4^h 3^{n-h})$
-- statement:
--   Let $I$ be an instance of #X3C with $n$ sets and $|U| = 3h$, satisfying the standing assumptions (every element of $U$ lies in some set, and $h < n$). For every exact cover $X$ of $I$,
--   $$\sum_{\sigma \in \Omega_{xc}(X)}\ \prod_{i=4h+1}^{4n} \frac{1}{i - C_{i,\sigma}} = \frac{(4h)!}{4^h\, 3^{n-h}} .$$
--
--   By Lemma 6.1 every factor $i - C_{i,\sigma}$ here is a positive integer. The right-hand side does not depend on $X$: each exact cover contributes the same weight to the limit of the proof of Theorem 6.3, which is what lets that limit count exact covers.
--
--   **Formalization Note.** Quantities as in `CountOrderings.NFree.Reduction`; the sum is computed in $\mathbb{R}$.
--
--   Differences from the source:
--   - generalization: a family $\mathcal{S} = \{S_1, \dots, S_n\}$ of $n$ (distinct) 3-sets → an indexed family $S_0, \dots, S_{n-1}$ in which two indices may carry the same 3-set; reason: the lemma only uses indices; for distinct sets this is exactly the paper's instance.
--   - encoding: $\Omega_{le}$ defined as $\{\sigma \mid \#\mathrm{LE}(P_{I,q})_\sigma > 0\}$ → the linear extensions of the edge poset of $E'$; reason: the paper proves the two sets equal on p. 16.
--   - encoding: the sum of reciprocals $1/(i - C_{i,\sigma})$ → the sum in ℝ; reason: every denominator is a positive integer (Lemma 6.1); same value.
--   - encoding: sets, universe elements and ordering positions numbered from 1 → zero-based Fin indices, with position p represented in rho and Ccount by p + 1 and the product index i still starting at 1; reason: bijective relabeling preserves the last i edges and every count.
-- source:
--   Arenas, Schild and Subercaseaux, Hardness of Counting Orderings: Taking Gadget Amplification to the Limit, STOC 2027 submission, p. 19 (PDF p. 20), Lemma 6.2; proof in Appendix A.11, pp. 35–37 (PDF pp. 36–38)

import Mathlib
import Definitions.Def_CountOrderings_NFree_Reduction

namespace CountOrderings.NFree

theorem lemma_6_2 (I : X3CInstance) (hI : I.Standing) (X : Finset (Fin I.n))
    (hX : X ∈ I.exactCovers) :
    ∑ σ ∈ omegaXC I X,
        ∏ i ∈ Finset.Icc (4 * I.h + 1) (4 * I.n), 1 / ((i : ℝ) - (Ccount σ i : ℝ)) =
      ((4 * I.h).factorial : ℝ) / ((4 : ℝ) ^ I.h * (3 : ℝ) ^ (I.n - I.h)) := by sorry

end CountOrderings.NFree
