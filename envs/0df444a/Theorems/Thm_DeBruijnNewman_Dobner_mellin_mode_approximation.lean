-- Prove2me | Theorems.Thm_DeBruijnNewman_Dobner_mellin_mode_approximation
-- name    : DeBruijnNewman.Dobner.mellin_mode_approximation
-- status  : Proved
-- author  : @adobner
-- created : 2026-09-24T22:34:12.73074+00:00
-- url     : https://prove2.me/theorems/6d260d38-6e4c-4a2a-a80c-f3e4220ccf7f
-- title:
--   Each Gaussian–Mellin coefficient approaches its damped Dirichlet term
-- statement:
--   Fix $t<0$, a strip $a\leq\operatorname{Re}s\leq b$ with $a<b$, and one positive integer $N$. The normalized individual coefficient satisfies
--
--   $$
--   \frac{B_{t,N}(s)}{\gamma_t(s)}
--   -\exp\!\left(\frac{t}{4}\log^2N-s\log N\right)
--   \longrightarrow0
--   $$
--
--   uniformly in that strip as $\operatorname{Im}s\to+\infty$.
--   Precisely, for each $\varepsilon>0$ there is a height $Y$ such that the norm of this difference is below $\varepsilon$ whenever $a\leq\operatorname{Re}s\leq b$ and $\operatorname{Im}s\geq Y$. The height may depend on $t,a,b,N,\varepsilon$.
--
--   This is the qualitative, fixed-coefficient consequence of Lemma 4(i). It identifies the damped Dirichlet term associated with one contour coefficient and provides the individual limits used in a subsequent summation argument. No uniformity in $N$ is asserted here.
--
--   **Formalization Note.** The natural-number index $n$ represents the positive integer $N=n+1$.
-- source:
--   Alexander Dobner, A proof of Newman's conjecture for the extended Selberg class, arXiv:2005.05142v2 (10 January 2026), https://arxiv.org/abs/2005.05142v2, Lemma 4(i), p. 16; steepest-descent proof pp. 19–22, especially equations (21)–(28). Fixed-time, fixed-strip, fixed-index consequence.

import Definitions.Def_DeBruijnNewman_Dobner_Mellin

theorem DeBruijnNewman.Dobner.mellin_mode_approximation (t : ℝ) (ht : t < 0)
    (a b : ℝ) (hab : a < b) (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ Y : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → Y ≤ s.im →
      ‖DeBruijnNewman.Dobner.normalizedMellinTerm t s n
        - DeBruijnNewman.Dobner.zetaTerm t s n‖ < ε := by sorry
