-- Prove2me | Theorems.Thm_CountOrderings_NFree_display_A12_limit
-- name    : CountOrderings.NFree.display_A12_limit
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:58:05.389087+00:00
-- url     : https://prove2.me/theorems/42c25298-105d-488f-9cf3-954475f4785d
-- title:
--   Appendix A.12, display — $\lim_{q\to-1}(q+1)^{4h}\sum_{\sigma\in\Omega_{le}}\chi_\sigma(q) = 4^{-h}3^{h-n}\,\#X3C(I)$
-- statement:
--   Let $I$ be an instance of #X3C with $n$ sets and $|U| = 3h$, satisfying the standing assumptions (every element of $U$ lies in some set, and $h < n$), and write $\chi_\sigma(q) = \prod_{i=1}^{4n} 1/(i + q\, C_{i,\sigma})$. Then the chain of equalities in the proof of Theorem 6.3 holds:
--   $$\lim_{q\to-1} (q+1)^{4h} \sum_{\sigma\in\Omega_{le}} \chi_\sigma(q) = \lim_{q\to-1} \sum_{X\in \mathrm{X3C}(I)}\ \sum_{\sigma\in\Omega_{xc}(X)} (q+1)^{4h}\chi_\sigma(q) = \frac{1}{(4h)!}\sum_{X\in \mathrm{X3C}(I)}\ \sum_{\sigma\in\Omega_{xc}(X)}\ \prod_{i=4h+1}^{4n}\frac{1}{i - C_{i,\sigma}} = \frac{1}{(4h)!}\sum_{X\in \mathrm{X3C}(I)} \frac{(4h)!}{4^h 3^{n-h}} = 4^{-h}\, 3^{h-n}\, \#\mathrm{X3C}(I).$$
--   Precisely: both limits exist and equal $4^{-h} 3^{h-n} \#\mathrm{X3C}(I)$, and the two finite expressions equal the same number.
--
--   Since $\sum_{\sigma \in \Omega_{le}} \chi_\sigma(q) = \#\mathrm{LE}(P_{I,q})/(4n+3hq+nq)!$ for positive integers $q$, this identity recovers $\#\mathrm{X3C}(I)$ from the rational function determined by the numbers of linear extensions of the N-free height-3 posets $P_{I,q}$.
--
--   **Formalization Note.** $q$ ranges over $\mathbb{R}$ and each limit is taken over a punctured neighbourhood of $-1$ (`𝓝[≠] (-1)`), so the value of the expressions at $q = -1$ itself (where some factors $i + q C_{i,\sigma}$ vanish and Lean's $1/0 = 0$ applies) plays no role. The other poles of $\chi_\sigma$, at $q = -i/C_{i,\sigma} \neq -1$, are isolated and do not affect the limit. The chain is stated as four facts, each ending in the final value.
--
--   Differences from the source:
--   - generalization: a family $\mathcal{S} = \{S_1, \dots, S_n\}$ of $n$ (distinct) 3-sets → an indexed family $S_0, \dots, S_{n-1}$ in which two indices may carry the same 3-set, and $\#\mathrm{X3C}(I)$ counts index sets; reason: the identity only uses indices; for distinct sets this is exactly the paper's instance and count.
--   - encoding: $\Omega_{le}$ defined as $\{\sigma \mid \#\mathrm{LE}(P_{I,q})_\sigma > 0\}$ → the linear extensions of the edge poset of $E'$; reason: the paper proves the two sets equal on p. 16.
--   - encoding: $\lim_{q\to-1}$ of a rational function of $q$ → `Filter.Tendsto` of the real function along the punctured neighbourhood `𝓝[≠] (-1)`; reason: the standard meaning of the limit; the punctured filter ignores the value at the pole.
--   - encoding: a chain of five equal expressions → a conjunction of four statements, each equating one expression (or the existence and value of its limit) with the final value $4^{-h}3^{h-n}\#\mathrm{X3C}(I)$; reason: equivalent to the chain.
--   - encoding: sets, universe elements and ordering positions numbered from 1 → zero-based Fin indices, with position p represented in rho and Ccount by p + 1 and the product index i still starting at 1; reason: bijective relabeling preserves the last i edges and every count.
-- source:
--   Arenas, Schild and Subercaseaux, Hardness of Counting Orderings: Taking Gadget Amplification to the Limit, STOC 2027 submission, pp. 37–38 (PDF pp. 38–39), Appendix A.12, display in the proof of Theorem 6.3

import Mathlib
import Definitions.Def_CountOrderings_NFree_Reduction

open Filter Topology

namespace CountOrderings.NFree

theorem display_A12_limit (I : X3CInstance) (hI : I.Standing) :
    Tendsto (fun q : ℝ => (q + 1) ^ (4 * I.h) * ∑ σ ∈ omegaLE I, chi σ q) (𝓝[≠] (-1))
        (𝓝 ((4 : ℝ) ^ (-(I.h : ℤ)) * (3 : ℝ) ^ ((I.h : ℤ) - I.n) * I.numExactCovers)) ∧
      Tendsto (fun q : ℝ => ∑ X ∈ I.exactCovers, ∑ σ ∈ omegaXC I X, (q + 1) ^ (4 * I.h) * chi σ q)
        (𝓝[≠] (-1))
        (𝓝 ((4 : ℝ) ^ (-(I.h : ℤ)) * (3 : ℝ) ^ ((I.h : ℤ) - I.n) * I.numExactCovers)) ∧
      1 / ((4 * I.h).factorial : ℝ) * ∑ X ∈ I.exactCovers, ∑ σ ∈ omegaXC I X,
          ∏ i ∈ Finset.Icc (4 * I.h + 1) (4 * I.n), 1 / ((i : ℝ) - (Ccount σ i : ℝ)) =
        (4 : ℝ) ^ (-(I.h : ℤ)) * (3 : ℝ) ^ ((I.h : ℤ) - I.n) * I.numExactCovers ∧
      1 / ((4 * I.h).factorial : ℝ) * ∑ _X ∈ I.exactCovers,
          ((4 * I.h).factorial : ℝ) / ((4 : ℝ) ^ I.h * (3 : ℝ) ^ (I.n - I.h)) =
        (4 : ℝ) ^ (-(I.h : ℤ)) * (3 : ℝ) ^ ((I.h : ℤ) - I.n) * I.numExactCovers := by sorry

end CountOrderings.NFree
