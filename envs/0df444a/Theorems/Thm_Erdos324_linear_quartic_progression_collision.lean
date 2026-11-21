-- Prove2me | Theorems.Thm_Erdos324_linear_quartic_progression_collision
-- name    : Erdos324.linear_quartic_progression_collision
-- status  : Proved
-- author  : @Mceppaglia
-- created : 2026-11-20T19:47:35.231329+00:00
-- url     : https://prove2.me/theorems/c1a527a8-c187-4f5c-afea-667e7f943f15
-- title:
--   Repeated pair sums for a progression of quartics $x^4+dx$
-- statement:
--   For every natural number $n$, put $d=-379828253655132800-2220222977058240n$ and $F_d(x)=x^4+dx$. There are positive integers $a<r<s<b$ with $0<F_d(a)<F_d(r)<F_d(s)<F_d(b)$ and $F_d(a)+F_d(b)=F_d(r)+F_d(s)$.
-- source:
--   Restricted results concerning Erdős problem 324, https://www.erdosproblems.com/324. John Leech, Some solutions of Diophantine equations (1957), https://doi.org/10.1017/S0305004100032850, supplied the classical equal-fourth-powers seed for the progression. Lander and Parkin, Equal Sums of Biquadrates (1966), Table I, row 5, https://www.jstor.org/stable/2003608, tabulate it. Browning, The polynomial sieve and equal sums of like polynomials, §3, equation (3.1), https://arxiv.org/abs/1306.6767, gives related coordinates for counting collisions. Matt directed the investigation. OpenAI Codex (Astra) developed the constructions and Lean proofs. Related earlier theorem for x^4+c x^2: https://prove2.me/theorems/46859084-43bf-49ae-8031-cf56665d52f9

import Mathlib

theorem Erdos324.linear_quartic_progression_collision (n : ℕ) :
    let d : ℤ := -(2220222977058240 * (n : ℤ) + 379828253655132800)
    let f : ℕ → ℤ := fun x => (x : ℤ)^4 + d * (x : ℤ)
    ∃ a r s b : ℕ,
      0 < a ∧ a < r ∧ r < s ∧ s < b ∧
      0 < f a ∧ f a < f r ∧ f r < f s ∧ f s < f b ∧
      f a + f b = f r + f s := by sorry
