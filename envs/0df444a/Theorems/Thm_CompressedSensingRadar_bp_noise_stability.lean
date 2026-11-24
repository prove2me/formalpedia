-- Prove2me | Theorems.Thm_CompressedSensingRadar_bp_noise_stability
-- name    : CompressedSensingRadar.bp_noise_stability
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T10:09:14.290439+00:00
-- url     : https://prove2.me/theorems/cf469525-1c12-41cf-9e3b-fb356a861023
-- title:
--   Proposition 3 (Donoho-Elad, Theorem 3): $\ell^1$-stability of BP under bounded noise
-- statement:
--   Let $\Phi\in\mathbb{C}^{N\times N^2}$ have unit-norm atoms and coherence $\mu$. Let $s$ be $K$-sparse, $T>0$, and let $y=\Phi s+e$ with noise $|e_n|\le\varepsilon$ for every $n$. Suppose
--
--   $$K<\frac{1+\mu}{2\mu+4\varepsilon\sqrt N/T}.$$
--
--   Then every solution $s^\star$ of the noise-aware basis pursuit $\min\|s'\|_1$ subject to $|(\Phi s'-y)_n|\le\varepsilon$ for all $n$ satisfies
--
--   $$\|s-s^\star\|_1\le T.$$
--
--   **Formalization Note** The basis pursuit program is the one of footnote 1 of the paper, with entrywise noise constraints. The stability parameter $T$ is taken positive, since it divides in the hypothesis.
-- source:
--   Herman and Strohmer, High-Resolution Radar via Compressed Sensing, arXiv:0803.2257v2 (2008), Appendix A, Proposition 3, p. 13 (citing Donoho and Elad, Signal Processing 86 (2006), Theorem 3); BP program of footnote 1, p. 2

import Mathlib
import Definitions.Def_CompressedSensingRadar_Basic

open MeasureTheory ProbabilityTheory

namespace CompressedSensingRadar

theorem bp_noise_stability (N : ℕ) (Φ : Matrix (Fin N) (Fin (N ^ 2)) ℂ) (hΦ : HasUnitAtoms Φ)
    (K : ℕ) (s : Fin (N ^ 2) → ℂ) (hs : IsSparse K s) (ε T : ℝ) (hT : 0 < T)
    (hK : (K : ℝ) < (1 + coherence Φ) / (2 * coherence Φ + 4 * ε * Real.sqrt N / T))
    (e : Fin N → ℂ) (he : ∀ n, ‖e n‖ ≤ ε) (sstar : Fin (N ^ 2) → ℂ)
    (hstar : IsNoisyBPSolution Φ (Φ.mulVec s + e) ε sstar) :
    norm1 (s - sstar) ≤ T := by sorry

end CompressedSensingRadar
