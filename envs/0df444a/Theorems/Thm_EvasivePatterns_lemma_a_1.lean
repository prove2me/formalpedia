-- Prove2me | Theorems.Thm_EvasivePatterns_lemma_a_1
-- name    : EvasivePatterns.lemma_a_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:27:14.487196+00:00
-- url     : https://prove2.me/theorems/deda4f08-9705-409b-86ef-6d2c1f06000f
-- title:
--   Lemma A.1 — large initial gap: every normalized homometric mate is $S$ or $m-S$
-- statement:
--   Let $S \subseteq [0, m]$ be a finite set of integers whose smallest positive point $p$ satisfies $p > m/2$. Then every **normalized homometric mate** $T$ of $S$, that is, every finite integer set with $\min T = 0$, $\max T = m$ and $\mathcal D(T) = \mathcal D(S)$, satisfies
--   $$
--   T = S \qquad\text{or}\qquad T = m - S .
--   $$
--   This is the case $k = 1$ of the rigidity theorem (Theorem 3.1).
--
--   Differences from the source:
--   - encoding: S ⊆ [0, m] with m real, p > m/2 → m an integer, m < 2p; reason: a normalized mate is an integer set with maximum m, so no mate exists for non-integer m; for integers p > m/2 is m < 2p
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), Appendix A.1, Lemma A.1, p.11 (PDF p.12), lines 365–366

import Mathlib
import Definitions.Def_EvasivePatterns_distMultiset

namespace EvasivePatterns

/-- **Lemma A.1 (the large initial gap).** If a finite integer set `S ⊆ [0, m]` has smallest
positive point `p > m/2`, then every normalized homometric mate is `S` or `m − S`.

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), Appendix A.1, Lemma A.1, printed p. 11 (PDF p. 12), lines 365–366; normalized
homometric mate: §2, printed p. 2 (PDF p. 3), lines 70–71.

**Formalization Note** `m` is an integer (a normalized mate is an integer set with maximum `m`).
"Smallest positive point `p`" is `p ∈ S`, `0 < p`, and `p ≤ x` for every positive `x ∈ S`;
`p > m/2` is `m < 2p`. A normalized homometric mate is a finite integer set `T` with `min T = 0`,
`max T = m` and `D(T) = D(S)`. `m − S` is the image of `S` under `x ↦ m − x`. -/
theorem lemma_a_1 (S : Finset ℤ) (m p : ℤ) (hS : ∀ x ∈ S, 0 ≤ x ∧ x ≤ m)
    (hpS : p ∈ S) (hp : 0 < p) (hpmin : ∀ x ∈ S, 0 < x → p ≤ x) (hpm : m < 2 * p)
    (T : Finset ℤ) (hTmin : T.min = (0 : WithTop ℤ)) (hTmax : T.max = (m : WithBot ℤ))
    (hTS : distMultiset T = distMultiset S) :
    T = S ∨ T = S.image (fun x => m - x) := by sorry

end EvasivePatterns
