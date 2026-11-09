-- Prove2me | Theorems.Thm_CyclicForrelation_Even_nonadaptive_upper_bound
-- name    : CyclicForrelation.Even.nonadaptive_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:33:05.068334+00:00
-- url     : https://prove2.me/theorems/98b97334-727d-41a6-89c9-b69b0a357786
-- title:
--   Theorem 10 — arbitrary-confidence nonadaptive estimation
-- statement:
--   Let $n\in\mathbb N$, $N=2^n$, let $k\ge4$ be even, and suppose $0<\varepsilon<1$ and $0<\delta<1/2$. There exist a natural cost $q$ and a randomized nonadaptive classical algorithm $A$ such that every private seed uses at most $q$ total oracle queries, every fixed input tuple is estimated to additive error $\varepsilon$ with probability at least $1-\delta$, and
--   $$q\le187k\min\{N,N^{1-2/k}\varepsilon^{-4/k}\ln(1/\delta)\}.$$
--   The logarithm remains inside the minimum, preserving exhaustive-query saturation at every confidence level. The existence claim ranges over the operational algorithm model, not a structure that assumes a variance bound or the desired performance.
--
--   **Formalization Note** Write $A_0=N^{1-2/k}\varepsilon^{-4/k}\ge1$. The p. 18 choice $q_0=\lceil16A_0\rceil$ gives failure at most $1/4$; $q_0\le17A_0$ and exhaustive evaluation give cost at most $17k\min(N,A_0)$. The smallest odd number $r\ge8\ln(1/\delta)$ is at most $11\ln(1/\delta)$ because $\delta<1/2$; the median failure is at most $e^{-r/8}\le\delta$. Selecting exhaustive evaluation whenever cheaper gives the displayed uniform constant $187=17\cdot11$.
--
--   Differences from the source:
--   - generalization: an O bound with an unspecified absolute constant → the numerical upper certificate 187, independent of n, k, ε, and δ; reason: the p. 18 estimator costs at most 17k min(N,A); odd median repetition with r≤11 ln(1/δ) and the exhaustive alternative yields 187k min(N,A ln(1/δ))
--   - encoding: minimum total worst-case nonadaptive oracle queries at success 2/3 → least achievable natural cost in the measurable private-seed query-list model; reason: queries are fixed before answers, postprocessing sees only answers and the seed, and exhaustive evaluation proves feasibility before minimization
--   - encoding: one-based sign-function tuples on the binary cube → zero-based finite indices and Boolean signs interpreted as real ±1; reason: these are bijective encodings, with the closing cycle edge and every input tuple preserved
--   - encoding: log(1/δ) up to a universal constant → the natural logarithm Real.log(1/δ); reason: changing the logarithm base only changes the already unspecified absolute constant; the certificate uses natural logarithms
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #333 (October 2026), p. 16, Theorem 10, Eq. (27); pp. 16–18, Eq. (28) and amplification paragraph

import Definitions.Def_CyclicForrelation_Even_complexity
import Definitions.Def_CyclicForrelation_Even_sampling

namespace CyclicForrelation.Even

/-- Theorem 10 at arbitrary confidence, with the log factor inside the saturation minimum. -/
theorem nonadaptive_upper_bound (n k : ℕ) (hk : 4 ≤ k) (heven : Even k)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    ∃ (q : ℕ) (A : NonadaptiveAlgorithm (Fin k × Cube n)),
      CostAtMost A q ∧ Estimates A (traceTarget n k) ε (1 - δ) ∧
      (q : ℝ) ≤ 187 * (k : ℝ) *
        min (cubeSize n : ℝ) (samplingScale n k ε * Real.log (1 / δ)) := by sorry

end CyclicForrelation.Even
