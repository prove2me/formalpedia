-- Prove2me | Theorems.Thm_CharacterSums_legendre_sum_two_forms_bound_one
-- name    : CharacterSums.legendre_sum_two_forms_bound_one
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T12:35:10.320037+00:00
-- url     : https://prove2.me/theorems/18c3827e-211d-496e-9331-e614fd217a19
-- title:
--   Sharp bound for a quadratic character sum over two linear forms
-- statement:
--   **The sharp constant for a quadratic character sum over two independent linear forms.**
--
--   Let $p$ be an odd prime, $\chi = \left(\tfrac{\cdot}{p}\right)$ the Legendre symbol, and let
--   $at+b$, $ct+d$ be linear forms with non-vanishing determinant $ad - bc \ne 0 \pmod p$. Then
--
--   $$\left|\sum_{t \bmod p} \chi(at+b)\,\chi(ct+d)\right| \;\le\; 1 .$$
--
--   This is the **sharp** form of the bound: the constant $1$ cannot be improved, because the sum
--   is in fact equal to $-\chi(ac)$ whenever $a, c \ne 0$, hence of modulus exactly $1$ in that
--   case. The trivial bound is $p$, so this is complete cancellation with the optimal constant.
--
--   The weaker bound with constant $2$ follows immediately and is what one usually records when the
--   degenerate cases ($a = 0$ or $c = 0$) are handled crudely; the sharp statement requires
--   treating those cases exactly rather than by a triangle-inequality estimate.
--
--   For two linear forms this is the exact analogue of the Weil bound
--   $|\sum_t \chi(f(t))| \le (\deg f - 1)\sqrt p$: with $f$ a product of two distinct linear
--   factors, $\deg f = 2$ and the bound reads $\le \sqrt p$ — but here the elementary evaluation
--   gives the far stronger constant $1$, independent of $p$, because the quadratic character of a
--   product of two linear forms can be evaluated in closed form.
--
--   **Formalization note.** `quadraticChar (ZMod p)` is Mathlib's quadratic character, valued in
--   $\mathbb{Z}$, so the sum and absolute value are integers and the bound $\le 1$ is an inequality
--   in $\mathbb{Z}$.
-- source:
--   Classical; the sharp elementary case of the Weil bound, see Iwaniec & Kowalski, *Analytic Number Theory*, §11.2, and Lidl & Niederreiter, *Finite Fields*, Ch. 5. Lean proof extracted from `Salt/HB/QuadCharSum.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace CharacterSums

theorem legendre_sum_two_forms_bound_one {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {a b c d : ZMod p} (h : a * d - b * c ≠ 0) :
    |∑ t : ZMod p, quadraticChar (ZMod p) (a * t + b) * quadraticChar (ZMod p) (c * t + d)|
      ≤ 1 := by sorry

end CharacterSums
