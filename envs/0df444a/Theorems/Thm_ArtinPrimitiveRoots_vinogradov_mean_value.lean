-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_vinogradov_mean_value
-- name    : ArtinPrimitiveRoots.vinogradov_mean_value
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T14:52:13.784205+00:00
-- url     : https://prove2.me/theorems/416e3626-285e-4638-887b-9d5dd7595c7c
-- title:
--   Lemma 3.2 of OpenAI's Prime Predecessors paper — Vinogradov's mean value theorem with degree-uniform constants, J_{s,k}(M) ≤ exp(C₁k^{C₂}) M^{2s−K+1/100}
-- statement:
--   There are constants $C_1, C_2 > 0$ such that for every integer $k \ge 2$ some integer $s$ with $k \le s \le C_1k^4$ satisfies
--
--   $$J_{s,k}(M) \le \exp(C_1k^{C_2})\,M^{2s - K + 1/100}\qquad\text{for every integer } M \ge 1,$$
--
--   where $K = k(k+1)/2$ and $J_{s,k}(M)$ is Vinogradov's count (`vinogradovCount`).
--
--   A step toward `log_phase_progression` (Lemma 3.3 of the same paper), which uses it with $k \ll (\log\log x)^2$; the constants are therefore uniform in the degree. The paper proves it by Linnik's $p$-adic iteration.
--
--   OpenAI, *Prime Predecessors with an Even Number of Prime Factors* (2026), p. 5: “Lemma 3.2 (A quantitative power-sum bound). There are absolute constants $C_1, C_2 > 0$ such that, for every integer $k \ge 2$, some integer $s$ with $k \le s \le C_1k^4$ satisfies $J_{s,k}(M) \le \exp(C_1k^{C_2})M^{2s-K+1/100}$ $(M \ge 1)$. (3.2)” On p. 4: “Writing $K = k(k+1)/2$”.
-- source:
--   OpenAI, Prime Predecessors with an Even Number of Prime Factors, OpenAI Math Release preprint, September 17, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Prime-Predecessors-with-an-Even-Number-of-Prime-Factors-September-17-2026/paper.pdf (Apache-2.0), p. 5, Lemma 3.2 (a quantitative power-sum bound: Vinogradov's mean value theorem)

import Mathlib
import Definitions.Def_ArtinVinogradov

namespace ArtinPrimitiveRoots

open Real

theorem vinogradov_mean_value :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ k : ℕ, 2 ≤ k →
      ∃ s : ℕ, k ≤ s ∧ (s : ℝ) ≤ C₁ * (k : ℝ) ^ 4 ∧ ∀ M : ℕ, 1 ≤ M →
        (vinogradovCount s k M : ℝ) ≤
          exp (C₁ * (k : ℝ) ^ C₂) *
            (M : ℝ) ^ (2 * (s : ℝ) - ((k * (k + 1) / 2 : ℕ) : ℝ) + 1 / 100) := by
  sorry

end ArtinPrimitiveRoots
