-- Prove2me | Theorems.Thm_CompressedSensingRadar_matrix_recovery_high_prob
-- name    : CompressedSensingRadar.matrix_recovery_high_prob
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T10:08:39.532971+00:00
-- url     : https://prove2.me/theorems/ce5282c3-3da1-4990-82a2-70e1aff0684d
-- title:
--   Theorem 2 (as proved): recovery with high probability for $K\le N/(16\log(N/\varepsilon))$
-- statement:
--   There is an absolute constant $c>0$ such that the following holds. Let $N\ge5$ be prime, $0<\varepsilon<1$, and let $K\ge1$ satisfy
--
--   $$K\le\frac{N}{16\log(N/\varepsilon)}.$$
--
--   Let $s\in\mathbb{C}^{N^2}$ be a random $K$-sparse vector: its support is a uniformly random $K$-subset and its nonzero coefficients are independent standard complex Gaussians. Let $H=\sum_is_iH_i$ and observe $y=Hf_A=\Phi_As$. Then for every $\vartheta\ge1$ with $\sqrt{\vartheta\log N/\log(N/\varepsilon)}\le c$, basis pursuit recovers $s$ with
--
--   $$\mathbb{P}\{\text{BP recovers }s\}>1-2\varepsilon^2-K^{-\vartheta}.$$
--
--   This is the paper's sparsity bound of order $N/\log N$ for compressed sensing radar with the Alltop pulse.
--
--   **Formalization Note** The paper says "for some sufficiently small $\varepsilon$". Its proof uses only $\varepsilon>0$ and $16\log(N/\varepsilon)>1$, which holds for every $\varepsilon\in(0,1)$ since $N\ge5$, so the statement is made for all $\varepsilon\in(0,1)$. The observation is written $\Phi_As$, which equals $Hf_A$ by eq. (7).
-- source:
--   Herman and Strohmer, High-Resolution Radar via Compressed Sensing, arXiv:0803.2257v2 (2008), Section III-E, Theorem 2, p. 5; proof in Appendix A-B, eqs. (15)-(17), p. 13

import Mathlib
import Definitions.Def_CompressedSensingRadar_Basic

open MeasureTheory ProbabilityTheory

namespace CompressedSensingRadar

theorem matrix_recovery_high_prob :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, N.Prime → 5 ≤ N → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ K : ℕ, 1 ≤ K → (K : ℝ) ≤ N / (16 * Real.log (N / ε)) →
      ∀ ϑ : ℝ, 1 ≤ ϑ → Real.sqrt (ϑ * Real.log N / Real.log (N / ε)) ≤ c →
        1 - 2 * ε ^ 2 - (K : ℝ) ^ (-ϑ) < bpProbRandom (gaborDict N (alltop N)) K := by sorry

end CompressedSensingRadar
