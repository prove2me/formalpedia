-- Prove2me | Theorems.Thm_ArithmeticFunctions_moebius_inv_dvd_lower_bound
-- name    : ArithmeticFunctions.moebius_inv_dvd_lower_bound
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:50:27.79604+00:00
-- url     : https://prove2.me/theorems/81c83c55-e88f-4487-b3d2-7aab0be469b7
-- title:
--   A Möbius orthogonality identity over the divisors of a squarefree number
-- statement:
--   **A Möbius sum restricted to the multiples of $l$ collapses to a single term.**
--
--   For $m$ squarefree and any $l$,
--
--   $$\sum_{\substack{d \mid m \\ l \mid d}} \mu(d) \;=\; \begin{cases} \mu(l) & \text{if } l = m,\\[2pt] 0 & \text{otherwise.}\end{cases}$$
--
--   If $l \nmid m$ the sum is empty. Otherwise write $d = l e$ with $e \mid m/l$; squarefreeness
--   makes $l$ and $e$ coprime, so $\mu(d) = \mu(l)\mu(e)$ and the sum factors as
--
--   $$\mu(l)\sum_{e \mid m/l}\mu(e) \;=\; \mu(l)\,[\,m/l = 1\,],$$
--
--   by the fundamental orthogonality $\sum_{e \mid n}\mu(e) = [n=1]$. So the only surviving case is
--   $m/l = 1$, i.e. $l = m$, where the value is $\mu(l)$.
--
--   The identity is the exact orthogonality relation that makes Selberg's sieve work: it is what
--   diagonalises the quadratic form in the sieve weights $\lambda_d$, letting a sum over pairs of
--   divisors be rewritten as a sum over a single index. Squarefreeness is essential — for $m$ with
--   a repeated prime factor, $l$ and $m/l$ need not be coprime and the factorisation of $\mu$ fails.
--
--   **Formalization note.** `μ` is `ArithmeticFunction.moebius`, cast to $\mathbb{Z}$; the guard
--   `if l ∣ d` restricts the divisor sum to the multiples of $l$.
-- source:
--   Standard in sieve theory; see Halberstam & Richert, *Sieve Methods*, Ch. 3, and Friedlander & Iwaniec, *Opera de Cribro*. Lean proof extracted from `Salt/Brun/SelbergPort.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace ArithmeticFunctions

theorem moebius_inv_dvd_lower_bound (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then (ArithmeticFunction.moebius d : ℤ) else 0)
      = if l = m then (ArithmeticFunction.moebius l : ℤ) else 0 := by sorry

end ArithmeticFunctions
