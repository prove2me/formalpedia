-- Prove2me | Theorems.Thm_BootstrapRecolorVerify_MetricGap_Supplement_claim_5_1
-- name    : BootstrapRecolorVerify.MetricGap.Supplement.claim_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:31:33.500405+00:00
-- url     : https://prove2.me/theorems/a88735d1-3815-4cea-9efe-ae4f4cf7f15d
-- title:
--   Claim 5.1 — Simultaneous Part I exceptional-level bound
-- statement:
--   For every fixed integer $r\ge2$, there is a threshold $n_0(r)\ge2$ such that for every even $n\ge n_0(r)$, drawing the entire Part I hierarchy by the original independent uniform matchings gives
--
--   $$\Pr\!\left[\forall j\in\{1,\ldots,r\},\ \frac{|F_j(G_r)|L^2}{N_r}\le\frac1n\right]\ge1-\frac{2rL^2}{n^2}.$$
--
--   Here $L=\beta_r\log n$, $N_r=n^{4^r}$, and $F_j(G_r)$ contains precisely descendants of the level-$j$ short-cycle edges marked at creation. All levels are controlled in the same event. No expansion, connectivity or acceptance condition is imposed. This bounds the exceptional contribution in the LP analysis for Theorem 3.1.
--
--   Differences from the source:
--   - encoding: fixed r≥2 and sufficiently large even n under the Part I construction → one threshold n₀(r)≥2 preceding every even n and every matching history; reason: this spells out the standing assumptions on pp.5–6 without excluding any sufficiently large even n
--   - generalization: with high probability (probability 1 − o(1)), with total failure O_r(n⁻² log² n) in the proof → failure at most 2rL²/n²; reason: an explicit vanishing failure bound is stronger than 1 − o(1) and implies it; the p.18 cycle count gives expected |F_j(G_j)|≤2N_j/n³ for sufficiently large n, and Markov and the union bound supply this concrete bound
--   - encoding: independent uniform perfect matchings → uniform counting on complete permutation-encoded matching histories; reason: constant multiplicities of the matching encodings preserve the raw law
-- source:
--   Konstantin Makarychev, STOC 2027 submission #1436 (October 2026), Claim 5.1, p.17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1436.pdf#page=17; PDF SHA-256 c6f69cddcebf9bb51692e022b1f2a1c3ca49babeba005dc1d6ce05e954bea358.

import Mathlib
import Definitions.Def_BootstrapRecolorVerify_MetricGap_Supplement_Hierarchy

namespace BootstrapRecolorVerify.MetricGap.Supplement

/-- Claim 5.1 p.17, quantified with the cycle/Markov estimate on p.18.
Probability is over raw independent uniform matchings, with no graph-property
or connectivity conditioning. Every exceptional level occurs in the event. -/
theorem claim_5_1 :
    ∀ r : ℕ, 2 ≤ r → ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → Even n →
        1 - 2 * r * lengthScale r n ^ 2 / (n : ℝ) ^ 2 ≤
          rawProbability (fun H : History n r => ExceptionalEvent H) := by sorry

end BootstrapRecolorVerify.MetricGap.Supplement
