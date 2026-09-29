-- Prove2me | Theorems.Thm_Diaz_power_support_interval_bound
-- name    : Diaz.power_support_interval_bound
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:17:55.41073+00:00
-- url     : https://prove2.me/theorems/ff2e39f8-94c2-4d57-af46-979eafa193eb
-- title:
--   A set with at most two representations of each difference is sparse
-- statement:
--   Let $T$ be a finite set of integers contained in an interval $[a,b]$, and suppose that for every non-zero $d$ there are at most two $n$ with $n, n+d \in T$. Then, writing $M = \#T$ and $N = b-a+1$ for the length of the interval,
--
--   $$M(M-1) \le 4(N-1).$$
--
--   **Where this sits.** This is the counting half of Carlo Perassi's power-support sparsity theorem. There $T = S(z) \cap I$ for
--
--   $$S(z) = \{\,n \in \mathbb{Z} : z^{n} \in \widetilde{\mathcal{L}}\,\},$$
--
--   and the hypothesis $\#\{n : n, n+d \in S(z)\} \le 2$ is supplied by the multiplier bound $\dim_{\bar{\mathbb{Q}}}\mathcal{M}_{z^{d}} \le 2$, itself a consequence of Roy's strong six exponentials theorem. Only the combinatorics is formalised here; the transcendence input is the hypothesis.
--
--   **The original form of the conclusion.** $M(M-1)/2 \le 2(N-1)$, equivalently
--
--   $$M \le \frac{1 + \sqrt{16N - 15}}{2},$$
--
--   from which $S(z)$ has zero asymptotic density. The displayed integer inequality is the same statement with the square root cleared, which is what the Lean states.
--
--   **Proof.** Map each ordered pair of distinct elements of $T$ to its difference. The image lies in $[a-b, b-a] \setminus \{0\}$, a set of $2(N-1)$ integers, and each fibre has at most two elements by hypothesis, since the pair is determined by its first coordinate once the difference is fixed. Hence $M^{2} - M \le 2 \cdot 2(N-1)$.
--
--   Elementary double counting. Novelty is not asserted.
--
--   **Source.** Carlo Perassi, unpublished apart from this node. The mathematics is his; this node only records one step of it in Lean, and claims no novelty of its own.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.power_support_interval_bound {a b : ℤ} (hab : a ≤ b) (T : Finset ℤ)
    (hT : ∀ n ∈ T, n ∈ Finset.Icc a b)
    (h2 : ∀ d : ℤ, d ≠ 0 → (T.filter (fun n => n + d ∈ T)).card ≤ 2) :
    (T.card : ℤ) * ((T.card : ℤ) - 1) ≤ 4 * (b - a) := by sorry
