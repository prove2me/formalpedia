-- Prove2me | Theorems.Thm_Erdos406_narkiewicz_bound
-- name    : Erdos406.narkiewicz_bound
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-25T11:37:32.392355+00:00
-- url     : https://prove2.me/theorems/f371d483-b58e-4d33-b82f-061ba6ac7f40
-- title:
--   Narkiewicz bound: $N(x) \le 1.62\,x^{\log_3 2}$
-- statement:
--   Let $N(x)$ count the exponents $n \le x$ for which the base-3 expansion of $2^n$ omits the digit $2$. Narkiewicz proved that for $x \ge 2$,
--
--   $$N(x) \le 1.62\, x^{\log_3 2}, \qquad \log_3 2 \approx 0.63093 .$$
--
--   This is the first power-saving bound toward Erdős Problem 406: it shows the exponents with the digit restriction are sparse, though it does not prove there are finitely many of them.
--
--   **Formalization Note** The constant $1.62$ is encoded as the rational $162/100$; $x^{\log_3 2}$ is real exponentiation with exponent $\log 2/\log 3$; and $x$ is a natural number with $x \ge 2$, so the real power is taken on a positive base.
-- source:
--   https://www.erdosproblems.com/406 — [Na80] W. Narkiewicz, Univ. Beograd. Publ. Elektrotehn. Fak. Ser. Mat. Fiz. (1980), 173–174

import Mathlib

namespace Erdos406

theorem narkiewicz_bound (x : ℕ) (hx : 2 ≤ x) :
    (((Finset.range (x + 1)).filter
      (fun n : ℕ => Nat.digits 3 (2 ^ n) ⊆ [0, 1])).card : ℝ)
        ≤ (162 : ℝ) / 100 * (x : ℝ) ^ (Real.log 2 / Real.log 3) := by
  sorry

end Erdos406
