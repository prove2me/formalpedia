-- Prove2me | Theorems.Thm_AddClosure_mem_of_add_closed_pair
-- name    : AddClosure.mem_of_add_closed_pair
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-05T20:17:48.365704+00:00
-- url     : https://prove2.me/theorems/afeba2bd-ddf7-4e50-8a67-c139a013eefe
-- title:
--   Two-step closure: $S \ni s$ closed under $+p,+q$ contains all $m \ge s+pq$ with $\gcd(p,q)\mid m-s$
-- statement:
--   This is a bounded, explicit form of the two-coin Frobenius (Chicken McNugget) theorem, phrased for sets closed under translations.
--
--   Let $S \subseteq \mathbb Z_{\ge 0}$, let $s \in S$, and let $p, q \ge 0$ with $p > 0$. Fix a bound $N$ and assume that $S$ is closed under adding $p$ and under adding $q$ as long as the result stays at most $N$:
--
--   1. $x \in S,\ x + p \le N \implies x + p \in S$;
--   2. $x \in S,\ x + q \le N \implies x + q \in S$.
--
--   Then every $m$ with
--
--   $$
--   s + pq \le m \le N \qquad\text{and}\qquad \gcd(p,q) \mid m - s
--   $$
--
--   belongs to $S$.
--
--   The threshold $s + pq$ depends only on $s, p, q$ and not on $S$; this uniformity is what is needed when the threshold must serve a whole class of sets at once, as in Lemma 4.9 of Brakensiek–Guruswami and its bounded Remark. Taking $N$ large (or $N = m$) gives the unbounded statement. The result applies to any argument of the form "a set containing $s$ and closed under two translations contains every large element of the right residue class", e.g. numerical semigroups, reachable sums, and periodicity arguments.
--
--   **Formalization Note** The divisibility $\gcd(p,q) \mid m - s$ uses natural-number subtraction, which is exact here because $m \ge s$. The case $q = 0$ is allowed, where $\gcd(p, 0) = p$.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, §4, proof of Lemma 4.9, p. 22 (the 'standard analysis of the Frobenius coin problem' invoked there; cf. the classical two-coin result of J. J. Sylvester, 1884)

import Mathlib

namespace AddClosure

/-- Two-generator closure (bounded Frobenius form). Let `S ⊆ ℕ` contain `s` and be closed under
adding `p` and adding `q` whenever the result is at most `N`, with `p > 0`. Then every `m` with
`s + p q ≤ m ≤ N` and `gcd(p, q) ∣ m - s` lies in `S`. -/
theorem mem_of_add_closed_pair {S : Set ℕ} {s p q N : ℕ} (hp : 0 < p)
    (hs : s ∈ S) (hP : ∀ x ∈ S, x + p ≤ N → x + p ∈ S)
    (hQ : ∀ x ∈ S, x + q ≤ N → x + q ∈ S) {m : ℕ} (hm : s + p * q ≤ m) (hmN : m ≤ N)
    (hg : Nat.gcd p q ∣ m - s) : m ∈ S := by sorry

end AddClosure
