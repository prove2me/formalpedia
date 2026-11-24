-- Prove2me | Theorems.Thm_CompressedSensingRadar_matrix_recovery_guaranteed_noise
-- name    : CompressedSensingRadar.matrix_recovery_guaranteed_noise
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T10:09:52.183818+00:00
-- url     : https://prove2.me/theorems/c0f93103-253a-4175-a00d-e2724e4d1917
-- title:
--   Theorem 3: stable recovery from noisy observations
-- statement:
--   Let $N\ge5$ be prime. Suppose $H=\sum_is_iH_i$ has a $K$-sparse representation $s$ in the time-frequency basis, and let $T>0$ with
--
--   $$K<\frac{\frac12(\sqrt N+1)}{1+2\varepsilon N/T}.$$
--
--   Suppose $y=Hf_A+e$ is observed, where every entry of the noise satisfies $|e_n|\le\varepsilon$. Then every solution $s^\star$ of the noise-aware basis pursuit $\min\|s'\|_1$ subject to $|(\Phi_As'-y)_n|\le\varepsilon$ for all $n$ satisfies
--
--   $$\|s-s^\star\|_1\le T.$$
--
--   **Formalization Note** The stability parameter $T$ is taken positive, since it divides in the hypothesis. The basis pursuit program is the one of footnote 1.
-- source:
--   Herman and Strohmer, High-Resolution Radar via Compressed Sensing, arXiv:0803.2257v2 (2008), Section III-E, Theorem 3, p. 5; proof in Appendix A-C, p. 13; BP program of footnote 1, p. 2

import Mathlib
import Definitions.Def_CompressedSensingRadar_Basic

open MeasureTheory ProbabilityTheory

namespace CompressedSensingRadar

theorem matrix_recovery_guaranteed_noise (N : ℕ) (hN : N.Prime) (h5 : 5 ≤ N) (K : ℕ)
    (s : Fin (N ^ 2) → ℂ) (hs : IsSparse K s) (ε T : ℝ) (hT : 0 < T)
    (hK : (K : ℝ) < (Real.sqrt N + 1) / 2 / (1 + 2 * ε * N / T))
    (e : Fin N → ℂ) (he : ∀ n, ‖e n‖ ≤ ε) (sstar : Fin (N ^ 2) → ℂ)
    (hstar : IsNoisyBPSolution (gaborDict N (alltop N))
      ((tfSynth N s).mulVec (alltop N) + e) ε sstar) :
    norm1 (s - sstar) ≤ T := by sorry

end CompressedSensingRadar
