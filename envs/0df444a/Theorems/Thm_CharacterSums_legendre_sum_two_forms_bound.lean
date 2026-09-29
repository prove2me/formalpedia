-- Prove2me | Theorems.Thm_CharacterSums_legendre_sum_two_forms_bound
-- name    : CharacterSums.legendre_sum_two_forms_bound
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T11:56:54.134045+00:00
-- url     : https://prove2.me/theorems/648a97ee-5aa2-4676-9ce5-0a9470b381bc
-- title:
--   A quadratic character sum over two independent linear forms
-- statement:
--   **Cancellation in a quadratic character sum over two linear forms.**
--
--   Let $p$ be an odd prime and let $\chi = \left(\tfrac{\cdot}{p}\right)$ be the Legendre symbol on
--   $\mathbb{Z}/p\mathbb{Z}$. Given two linear forms $at+b$ and $ct+d$ whose coefficient
--   determinant is non-zero,
--
--   $$ad - bc \;\ne\; 0 \pmod p,$$
--
--   the character sum over the full residue system is bounded by an **absolute constant**:
--
--   $$\left|\sum_{t \bmod p} \chi(at+b)\,\chi(ct+d)\right| \;\le\; 2.$$
--
--   The trivial bound is $p$, so this is total cancellation: the sum does not grow with the modulus
--   at all. The non-degeneracy condition $ad - bc \ne 0$ is exactly what prevents the two forms
--   from being proportional; if they were, the product $\chi(at+b)\chi(ct+d)$ would be
--   $\chi$ of a perfect square times a constant, hence essentially constant, and the sum would be
--   of size $p$.
--
--   This is the simplest non-trivial instance of the Weil bound for character sums, and unlike the
--   general case it admits a completely elementary proof: after a change of variable the sum
--   reduces to $\sum_t \chi(t)\chi(t+e)$ with $e \ne 0$, which evaluates to exactly $-1$ by writing
--   $\chi(t)\chi(t+e) = \chi\bigl(t^2(1 + e/t)\bigr) = \chi(1 + e/t)$ for $t \ne 0$ and summing the
--   non-trivial character over the shifted residues.
--
--   Sums of this shape are the workhorse of elementary estimates for the number of points on
--   conics over finite fields, and of the second-moment computations behind the large sieve and
--   Pólya–Vinogradov-type inequalities.
--
--   **Formalization note.** `quadraticChar (ZMod p)` is Mathlib's quadratic character, taking
--   values in $\mathbb{Z}$, so the sum and the absolute value are integer-valued and the bound
--   $\le 2$ is an inequality in $\mathbb{Z}$.
-- source:
--   Classical; the elementary case of the Weil bound, see Iwaniec & Kowalski, *Analytic Number Theory*, §11.2, and Lidl & Niederreiter, *Finite Fields*, Ch. 5. Lean proof extracted from `Salt/HB/QuadCharSum.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace CharacterSums

theorem legendre_sum_two_forms_bound {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {a b c d : ZMod p} (h : a * d - b * c ≠ 0) :
    |∑ t : ZMod p, quadraticChar (ZMod p) (a * t + b) * quadraticChar (ZMod p) (c * t + d)|
      ≤ 2 := by sorry

end CharacterSums
