-- Prove2me | Theorems.Thm_DeBruijnNewman_Dobner_mellin_uniform_majorant
-- name    : DeBruijnNewman.Dobner.mellin_uniform_majorant
-- status  : Proved
-- author  : @adobner
-- created : 2026-09-24T22:34:47.200006+00:00
-- url     : https://prove2.me/theorems/5b2ef1e0-8b8a-4d7e-b64d-bd8f74d3a863
-- title:
--   A summable bound for all normalized Gaussian–Mellin coefficients
-- statement:
--   Fix $t<0$ and $a<b$. There are constants $C>0$ and $Y\geq1$ such that, simultaneously for every positive integer $N$ and every $s$ with $a\leq\operatorname{Re}s\leq b$ and $\operatorname{Im}s\geq Y$,
--
--   $$
--   \left|\frac{B_{t,N}(s)}{\gamma_t(s)}\right|
--   \leq C\exp\!\left(\frac{t}{40}\log^2N\right).
--   $$
--
--   The right-hand side is summable over $N$, giving a majorant suitable for passing from individual coefficient limits to a limit of their sum. Both constants may depend on the fixed time and strip, but are independent of $N$ and $\operatorname{Im}s$. No uniformity as $t\to0$ is asserted.
--
--   This is a weakened fixed-strip consequence of Lemma 4(ii)–(iii) together with the paper's lower bound for $\gamma_t$. The coefficient $1/40$ is chosen to give a single bound covering all positive integers.
--
--   **Formalization Note.** The natural-number index $n$ represents the positive integer $N=n+1$.
-- source:
--   Alexander Dobner, A proof of Newman's conjecture for the extended Selberg class, arXiv:2005.05142v2 (10 January 2026), https://arxiv.org/abs/2005.05142v2, Lemma 4(ii)–(iii), p. 16, with proofs pp. 19–24; the gamma_t lower bound in equation (27), p. 22. The exponent 1/40 is a deliberate weakening for a fixed strip and fixed negative time.

import Definitions.Def_DeBruijnNewman_Dobner_Mellin

theorem DeBruijnNewman.Dobner.mellin_uniform_majorant (t : ℝ) (ht : t < 0)
    (a b : ℝ) (hab : a < b) :
    ∃ C Y : ℝ, 0 < C ∧ 1 ≤ Y ∧
      ∀ s : ℂ, a ≤ s.re → s.re ≤ b → Y ≤ s.im → ∀ n : ℕ,
        ‖DeBruijnNewman.Dobner.normalizedMellinTerm t s n‖ ≤
          C * Real.exp (t / 40 * Real.log ((n : ℝ) + 1) ^ 2) := by sorry
