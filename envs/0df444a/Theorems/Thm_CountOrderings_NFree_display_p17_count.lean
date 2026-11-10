-- Prove2me | Theorems.Thm_CountOrderings_NFree_display_p17_count
-- name    : CountOrderings.NFree.display_p17_count
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:58:01.758366+00:00
-- url     : https://prove2.me/theorems/e4323bcb-c4a5-4b0d-a571-fe82b6c71c00
-- title:
--   §6, display on p. 17 — $\#LE(P_{I,q})_\sigma = (4n+3hq+nq)!\prod_{i=1}^{4n} 1/(i+q\,C_{i,\sigma})$
-- statement:
--   Let $I$ be an instance of #X3C with $n$ sets and $|U| = 3h$, satisfying the paper's standing assumptions (every element of $U$ lies in some set, and $h < n$), and let $q \ge 1$ be an integer. For every ordering $\sigma \in \Omega_{le}$ of the edge set $E'$, the number of linear extensions of the edge poset $P_{I,q}$ whose projection down to $E'$ coincides with $\sigma$ is
--   $$\#\mathrm{LE}(P_{I,q})_\sigma = (4n + 3hq + nq)!\ \prod_{i=1}^{4n} \frac{1}{i + q \cdot C_{i,\sigma}} ,$$
--   where $C_{i,\sigma}$ counts the groups of $q$ copied edges attached to the last $i$ edges of $\sigma$ (definition `CountOrderings.NFree.Reduction`).
--
--   This is the first step of the proof of Theorem 6.3: fixing $\sigma$ turns the remaining constraints into a tree poset, and the hook-length formula (Lemma 2.2) counts its linear extensions. Summing over $\sigma$ expresses $\#\mathrm{LE}(P_{I,q})/(4n+3hq+nq)!$ as $\sum_{\sigma \in \Omega_{le}} \chi_\sigma(q)$.
--
--   **Formalization Note.** The identity is stated in $\mathbb{R}$. Sets, universe elements and copies are indexed from $0$; the position $p$ of $\sigma : \{0,\dots,4n-1\} \to E'$ is the paper's position $p+1$.
--
--   Differences from the source:
--   - generalization: a family $\mathcal{S} = \{S_1, \dots, S_n\}$ of $n$ (distinct) 3-sets → an indexed family $S_0, \dots, S_{n-1}$ in which two indices may carry the same 3-set; reason: the construction and the count only use indices; for distinct sets this is exactly the paper's instance.
--   - encoding: $\Omega_{le}$ defined as $\{\sigma \mid \#\mathrm{LE}(P_{I,q})_\sigma > 0\}$ → the linear extensions of the edge poset of $E'$; reason: the paper proves the two sets equal on p. 16.
--   - encoding: the identity between rationals → the same identity in ℝ; reason: same value.
--   - encoding: sets, universe elements and ordering positions numbered from 1 → zero-based Fin indices, with position p represented in rho and Ccount by p + 1 and the product index i still starting at 1; reason: bijective relabeling preserves the last i edges and every count.
-- source:
--   Arenas, Schild and Subercaseaux, Hardness of Counting Orderings: Taking Gadget Amplification to the Limit, STOC 2027 submission, p. 17 (PDF p. 18), §6, display for #LE(P_{I,q})_σ

import Mathlib
import Definitions.Def_CountOrderings_NFree_Reduction

namespace CountOrderings.NFree

theorem display_p17_count (I : X3CInstance) (hI : I.Standing) (q : ℕ) (hq : 1 ≤ q)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (hσ : σ ∈ omegaLE I) :
    (linExtCountGiven I q σ : ℝ) =
      ((4 * I.n + 3 * I.h * q + I.n * q).factorial : ℝ) *
        ∏ i ∈ Finset.Icc 1 (4 * I.n), 1 / ((i : ℝ) + (q : ℝ) * (Ccount σ i : ℝ)) := by sorry

end CountOrderings.NFree
