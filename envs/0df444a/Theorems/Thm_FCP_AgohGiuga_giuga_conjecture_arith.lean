-- Prove2me | Theorems.Thm_FCP_AgohGiuga_giuga_conjecture_arith
-- name    : FCP.AgohGiuga.giuga_conjecture_arith
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T21:17:46.55298+00:00
-- url     : https://prove2.me/theorems/cfd804b3-fea5-4679-a1e8-d43b16ad4b88
-- title:
--   Giuga's conjecture in arithmetic form: no composite Giuga--Carmichael number
-- statement:
--   **Giuga's conjecture, arithmetic form.** Let $n \ge 2$ be an integer and suppose that for every prime $p$ dividing $n$ both
--
--   $$p \;\Big|\; \frac{n}{p} - 1 \qquad\text{and}\qquad p - 1 \;\Big|\; \frac{n}{p} - 1$$
--
--   hold. Then $n$ is prime.
--
--   Equivalently: no composite number is simultaneously a Giuga number and a Carmichael number. This is the open kernel of the Agoh--Giuga conjecture. By Giuga's criterion, an integer $n \ge 2$ satisfies $\sum_{i=1}^{n-1} i^{\,n-1} \equiv -1 \pmod n$ exactly when the two displayed families of divisibilities hold, so the conjecture "the congruence forces primality" is equivalent to the statement above. A composite $n$ satisfying the hypotheses is known to have at least $13{,}800$ digits (Borwein, Borwein, Borwein and Girgensohn, 1996), and later computations push the bound much further.
--
--   Primes satisfy the hypotheses trivially: for $n = p$ prime the only prime divisor is $p$ itself, $n/p - 1 = 0$, and every number divides $0$.
--
--   **Formalization Note** All arithmetic is in the natural numbers; $n/p$ is exact division since $p \mid n$, and the subtractions are truncated natural subtraction, which is harmless because $p \ge 2$ and $n/p \ge 1$.
-- source:
--   Giuga, Su una presumibile proprieta caratteristica dei numeri primi, Ist. Lombardo Sci. Lett. Rend. A 83 (1950), 511-528; D. Borwein, J. M. Borwein, P. B. Borwein, R. Girgensohn, Giuga's conjecture on primality, Amer. Math. Monthly 103 (1996), 40-50; https://en.wikipedia.org/wiki/Agoh-Giuga_conjecture (section 'Status': a composite n satisfies the congruence if and only if it is both a Carmichael number and a Giuga number)

import Mathlib

namespace FCP.AgohGiuga

theorem giuga_conjecture_arith (n : ℕ) (hn : 2 ≤ n)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → p ∣ n / p - 1 ∧ (p - 1) ∣ n / p - 1) :
    n.Prime := by sorry

end FCP.AgohGiuga
