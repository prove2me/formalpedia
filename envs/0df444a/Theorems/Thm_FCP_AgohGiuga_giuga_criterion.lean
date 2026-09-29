-- Prove2me | Theorems.Thm_FCP_AgohGiuga_giuga_criterion
-- name    : FCP.AgohGiuga.giuga_criterion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T21:17:46.867792+00:00
-- url     : https://prove2.me/theorems/f47cdc6e-0596-4812-b182-8dac3e22e880
-- title:
--   Giuga's criterion for the congruence $\sum_{i<n} i^{n-1} \equiv -1 \pmod n$
-- statement:
--   **Giuga's criterion.** Let $n \ge 2$ be an integer. Then the Giuga congruence
--
--   $$\sum_{i=1}^{n-1} i^{\,n-1} \equiv -1 \pmod{n}$$
--
--   holds if and only if for every prime $p$ dividing $n$ one has
--
--   $$p \;\Big|\; \frac{n}{p} - 1 \qquad\text{and}\qquad p - 1 \;\Big|\; \frac{n}{p} - 1 .$$
--
--   The first family of conditions says that $n$ is a Giuga number (in the usual sense, extended here to prime $n$, for which $n/p - 1 = 0$ and the conditions are vacuous); the second family is Korselt's criterion in its $n/p$ form, and together with the first it says that $n$ is a Carmichael number. The criterion is the arithmetic heart of the Agoh--Giuga conjecture: it converts the congruence, a statement about a sum of $n-1$ large powers, into finitely many divisibility conditions on the prime factorisation of $n$, and it is the reason a counterexample to the conjecture is known to be simultaneously a Carmichael number and a Giuga number.
--
--   Note that the first condition forces $n$ to be squarefree: if $p^2 \mid n$ then $p \mid n/p$, which is incompatible with $p \mid n/p - 1$.
--
--   **Formalization Note** The sum is taken over the integers $i$ with $0 < i < n$, and all arithmetic is in the natural numbers, so the congruence $\sum i^{n-1} \equiv -1 \pmod n$ is written in the equivalent divisibility form $n \mid 1 + \sum_{i=1}^{n-1} i^{n-1}$. The subtractions $n/p - 1$ and $p - 1$ are truncated natural subtraction, which is harmless because $p \ge 2$ and $n/p \ge 1$ for every prime divisor $p$ of $n$.
-- source:
--   Giuga, Su una presumibile proprieta caratteristica dei numeri primi, Ist. Lombardo Sci. Lett. Rend. A 83 (1950), 511-528; D. Borwein, J. M. Borwein, P. B. Borwein, R. Girgensohn, Giuga's conjecture on primality, Amer. Math. Monthly 103 (1996), 40-50; https://en.wikipedia.org/wiki/Agoh-Giuga_conjecture (section 'Status': a composite n satisfies the congruence if and only if it is both a Carmichael number and a Giuga number)

import Mathlib

namespace FCP.AgohGiuga

theorem giuga_criterion (n : ℕ) (hn : 2 ≤ n) :
    n ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1) ↔
      ∀ p : ℕ, p.Prime → p ∣ n → p ∣ n / p - 1 ∧ (p - 1) ∣ n / p - 1 := by sorry

end FCP.AgohGiuga
