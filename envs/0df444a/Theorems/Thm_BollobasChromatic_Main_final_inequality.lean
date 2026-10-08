-- Prove2me | Theorems.Thm_BollobasChromatic_Main_final_inequality
-- name    : BollobasChromatic.Main.final_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:08:27.109839+00:00
-- url     : https://prove2.me/theorems/c5a2f3a4-594c-43ae-81f3-5f5d0caf64bb
-- title:
--   Proof of Theorem 4, p. 53 — n/s₁ + n₁ < (n/s₀)(1 + 3 log log n/log n) for n₁ = O(n/(log n)²)
-- statement:
--   Let $0<p<1$ be fixed, $d=1/(1-p)$, $s_0=[2\log_d n-\log_d\log_d n+2\log_d(e/2)+1]$ and $s_1=s_0-\lfloor 5\log_d\log n\rfloor$. For every constant $C$, for all large $n$ and every natural number $m\le C\,n/(\log n)^2$,
--   $$
--   \frac n{s_1}+m<\frac n{s_0}\Bigl(1+\frac{3\log\log n}{\log n}\Bigr).
--   $$
--
--   With $m=n_1$ this closes the proof of Theorem 4: the greedy colouring uses at most $n/s_1+n_1$ colours.
--
--   **Formalization Note** The page prints $n/s_1$ also on the right-hand side; the theorem is about $s_0$, and the stated inequality with $n/s_0$ on the right is the one that yields it (it holds because $s_0/s_1=1+(5/2+o(1))\log\log n/\log n$). Because the page's $n_1\le n/(\log n)^2$ is false with constant $1$ (see the milestone on $n_1$), the inequality is stated for every $m\le C\,n/(\log n)^2$, for every constant $C$.
-- source:
--   Bollobás, The chromatic number of random graphs, Combinatorica 8 (1988), p. 53, proof of Theorem 4, last display

import Mathlib
import Definitions.Def_BollobasChromatic_Main_Setting

namespace BollobasChromatic.Main

open Filter Topology Asymptotics

theorem final_inequality (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, (m : ℝ) ≤ C * n / Real.log (n : ℝ) ^ 2 →
      (n : ℝ) / (s1 p n : ℝ) + m <
        (n : ℝ) / (s0 p n : ℝ) * (1 + 3 * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) := by sorry

end BollobasChromatic.Main
