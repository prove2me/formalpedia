-- Prove2me | Theorems.Thm_CountOrderings_NFree_lemma_6_1
-- name    : CountOrderings.NFree.lemma_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:58:11.877697+00:00
-- url     : https://prove2.me/theorems/23cfa541-bb78-4ce8-b5e3-33c65aaab037
-- title:
--   Lemma 6.1 — exact-cover orderings are exactly those with $C_{i,\sigma} = i$ on $[4h]$
-- statement:
--   Let $I$ be an instance of #X3C with $n$ sets and $|U| = 3h$, satisfying the standing assumptions (every element of $U$ lies in some set, and $h < n$). Let $\sigma \in \Omega_{le}$. Then:
--
--   1. If $\sigma \in \Omega_{xc}(X)$ for some exact cover $X$, then
--   $$C_{i,\sigma} = i \quad (1 \le i \le 4h) \qquad\text{and}\qquad C_{i,\sigma} < i \quad (4h+1 \le i \le 4n).$$
--   2. If $\sigma$ induces no exact cover, then the set $B_\sigma = \{ i \in \{1, \dots, 4h\} \mid C_{i,\sigma} < i\}$ is non-empty.
--
--   In the proof of Theorem 6.3, a factor $i + q\, C_{i,\sigma}$ of $\chi_\sigma(q)$ vanishes at $q = -1$ exactly when $C_{i,\sigma} = i$; the lemma says that $\chi_\sigma$ has a pole of order $4h$ at $q = -1$ exactly for the orderings that induce an exact cover, and of smaller order otherwise.
--
--   **Formalization Note.** Quantities as in `CountOrderings.NFree.Reduction`; "$\sigma$ induces no exact cover" is "there is no $X \in \mathrm{X3C}(I)$ with $\sigma \in \Omega_{xc}(X)$".
--
--   Differences from the source:
--   - generalization: a family $\mathcal{S} = \{S_1, \dots, S_n\}$ of $n$ (distinct) 3-sets → an indexed family $S_0, \dots, S_{n-1}$ in which two indices may carry the same 3-set; reason: the lemma only uses indices; for distinct sets this is exactly the paper's instance.
--   - encoding: $\Omega_{le}$ defined as $\{\sigma \mid \#\mathrm{LE}(P_{I,q})_\sigma > 0\}$ → the linear extensions of the edge poset of $E'$; reason: the paper proves the two sets equal on p. 16.
--   - encoding: sets, universe elements and ordering positions numbered from 1 → zero-based Fin indices, with position p represented in rho and Ccount by p + 1 and the product index i still starting at 1; reason: bijective relabeling preserves the last i edges and every count.
-- source:
--   Arenas, Schild and Subercaseaux, Hardness of Counting Orderings: Taking Gadget Amplification to the Limit, STOC 2027 submission, p. 18 (PDF p. 19), Lemma 6.1; proof in Appendix A.10, p. 35 (PDF p. 36)

import Mathlib
import Definitions.Def_CountOrderings_NFree_Reduction

namespace CountOrderings.NFree

theorem lemma_6_1 (I : X3CInstance) (hI : I.Standing) (σ : Fin (4 * I.n) ≃ OrigEdge I)
    (hσ : σ ∈ omegaLE I) :
    (∀ X ∈ I.exactCovers, σ ∈ omegaXC I X →
        (∀ i ∈ Finset.Icc 1 (4 * I.h), Ccount σ i = i) ∧
          ∀ i ∈ Finset.Icc (4 * I.h + 1) (4 * I.n), Ccount σ i < i) ∧
      ((¬ ∃ X ∈ I.exactCovers, σ ∈ omegaXC I X) →
        ((Finset.Icc 1 (4 * I.h)).filter (fun i => Ccount σ i < i)).Nonempty) := by sorry

end CountOrderings.NFree
