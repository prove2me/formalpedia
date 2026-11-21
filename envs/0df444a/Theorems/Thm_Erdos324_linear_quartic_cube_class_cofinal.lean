-- Prove2me | Theorems.Thm_Erdos324_linear_quartic_cube_class_cofinal
-- name    : Erdos324.linear_quartic_cube_class_cofinal
-- status  : Proved
-- author  : @Mceppaglia
-- created : 2026-11-20T19:49:55.328595+00:00
-- url     : https://prove2.me/theorems/8b9982bd-8391-43f8-b205-2a633e7692c8
-- title:
--   Arbitrarily large pair-sum collisions in a cube class of quartics $x^4+dx$
-- statement:
--   Fix an integer $d$ in the progression $-379828253655132800-2220222977058240n$ with $n\ge 0$, and suppose $d/(-349520)$ is the cube of a rational number. Put $F_d(x)=x^4+dx$. For every natural cutoff $N$ there are integers $N<a<r<s<b$ with $N<F_d(a)<F_d(r)<F_d(s)<F_d(b)$ and $F_d(a)+F_d(b)=F_d(r)+F_d(s)$. The coefficient stays fixed as $N$ varies.
-- source:
--   Restricted results concerning Erdős problem 324, https://www.erdosproblems.com/324. John Leech, Some solutions of Diophantine equations (1957), https://doi.org/10.1017/S0305004100032850, supplied the classical equal-fourth-powers seed for the progression. Lander and Parkin, Equal Sums of Biquadrates (1966), Table I, row 5, https://www.jstor.org/stable/2003608, tabulate it. Browning, The polynomial sieve and equal sums of like polynomials, §3, equation (3.1), https://arxiv.org/abs/1306.6767, gives related coordinates for counting collisions. Matt directed the investigation. OpenAI Codex (Astra) developed the constructions and Lean proofs. Related earlier theorem for x^4+c x^2: https://prove2.me/theorems/46859084-43bf-49ae-8031-cf56665d52f9

import Mathlib

theorem Erdos324.linear_quartic_cube_class_cofinal (d : ℤ)
    (hsize : d ≤ -379828253655132800)
    (hres : (-d) % 2220222977058240 = 170124578173760)
    (hcube : ∃ q : ℚ, (d : ℚ) / (-349520) = q^3) (N : ℕ) :
    let f : ℕ → ℤ := fun x => (x : ℤ)^4 + d * (x : ℤ)
    ∃ a r s b : ℕ,
      N < a ∧ a < r ∧ r < s ∧ s < b ∧
      (N : ℤ) < f a ∧ f a < f r ∧ f r < f s ∧ f s < f b ∧
      f a + f b = f r + f s := by sorry
