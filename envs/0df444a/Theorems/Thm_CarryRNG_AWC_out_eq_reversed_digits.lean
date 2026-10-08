-- Prove2me | Theorems.Thm_CarryRNG_AWC_out_eq_reversed_digits
-- name    : CarryRNG.AWC.out_eq_reversed_digits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:28:21.616984+00:00
-- url     : https://prove2.me/theorems/63985aea-1e23-474e-a700-ae63df7b53a2
-- title:
--   §4.2 — the add-with-carry digits are the base-$b$ digits of $k/(b^r + b^s - 1)$ in reverse order
-- statement:
--   Let $b \ge 2$ be a base, $0 < s < r$ lags, $m = b^r + b^s - 1$, and let $x$ be a seed other than the trivial seed $(b-1, \dots, b-1, 1)$, with generated digit sequence $x_1, x_2, \dots$. Then for every length $C$ there is an integer $k$ with $0 \le k < m$, and $k > 0$ exactly when $x \ne (0, \dots, 0, 0)$, such that the generated digits $x_{r+1}, \dots, x_C$, read backwards from $x_C$, are the leading base-$b$ digits of $k/m$:
--
--   $$
--   x_n = d_{C+1-n}(k/m) \qquad \text{for all } r + 1 \le n \le C ,
--   $$
--
--   where $d_j(k/m)$ is the $j$-th base-$b$ digit of $k/m$ after the point. In the paper's words, the reversed digits of an arbitrarily long finite string formed by $x_n = x_{n-r} + x_{n-s} + c \bmod b$ are those of a proper fraction $k/m$; for $b = 10$, $r = 2$, $s = 1$ and seed $(1, 2, 0)$, the digits $x_3, \dots, x_{12}$ reversed are $8348623853$, the first ten digits of $91/109$.
--
--   The trivial seed $(b-1, \dots, b-1, 1)$ is excluded because it produces the digit $b - 1$ forever, the expansion of $m/m = 1$, which is not a proper fraction.
--
--   **Formalization Note** The integer $k$ depends on $C$, as in the paper (the string length determines the tableau). An equivalent closed form: there is $u \in \mathbb{Z}/m$, with $u = 0$ iff $x$ is the zero seed, such that $x_n = \lfloor b \cdot (u\, b^{-n} \bmod m) / m \rfloor$ for all $n \ge r + 1$. No primality of $m$ is assumed.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), p. 468, Section 4.2; p. 471, Section 4.5 ("the base-b digits generated are those of the expansion of k/m in reverse order")

import Mathlib
import Definitions.Def_CarryRNG_AWC_out
import Definitions.Def_CarryRNG_AWC_zeroSeed
import Definitions.Def_CarryRNG_AWC_topSeed
import Definitions.Def_CarryRNG_AWC_modulus
import Definitions.Def_CarryRNG_AWC_digit

namespace CarryRNG.AWC

theorem out_eq_reversed_digits (b : ℕ) (L : Lags) (hb : 2 ≤ b) (z : State b L.r)
    (htop : z ≠ topSeed b L.r hb) (C : ℕ) :
    ∃ k : ℕ, k < modulus b L ∧ (0 < k ↔ z ≠ zeroSeed b L.r hb) ∧
      ∀ n : ℕ, L.r + 1 ≤ n → n ≤ C → out b L z n = digit b (modulus b L) k (C + 1 - n) := by sorry

end CarryRNG.AWC
