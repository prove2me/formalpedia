-- Prove2me | Theorems.Thm_BootstrapRecolorVerify_MetricGap_Supplement_theorem_3_1
-- name    : BootstrapRecolorVerify.MetricGap.Supplement.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:32:19.567957+00:00
-- url     : https://prove2.me/theorems/fae4fbd9-f512-48d4-b394-f916e39ecc7e
-- title:
--   Theorem 3.1 — Fixed-depth random metric-LP gap
-- statement:
--   For every fixed integer $r\ge2$ there are constants $\gamma_r>0$, $A_r^{\mathrm{fail}}>0$ and a threshold $n_0(r)\ge2$, all chosen before the graph size and history, such that for every even $n\ge n_0(r)$ the Part I random construction satisfies
--
--   $$\Pr\!\left[\begin{gathered}\text{every internal cloud is connected, the computed instance }I\text{ is valid},\\ |T|=n^{4^r},\quad \operatorname{MetricLP}(I)>0,\\ \frac{\operatorname{OPT}(I)}{\operatorname{MetricLP}(I)}\ge\gamma_r(\log |T|)^{r/(r+1)}\end{gathered}\right]\ge1-A_r^{\mathrm{fail}}\frac{(\log n)^2}{n^2}.$$
--
--   Probability is under the original product-uniform matching law. On the connected event, $I$ is the terminal augmentation of this history, with the original multigraph terminal metric and the published metric relaxation. No good-history predicate is assumed and no existential replacement instance is substituted. This is the construction-specific companion theorem in Part I.
--
--   Differences from the source:
--   - encoding: fixed r≥2 and sufficiently large even n under the Part I construction → one threshold n₀(r)≥2 preceding every even n and every matching history; reason: this spells out the standing assumptions on pp.5–6 without excluding any sufficiently large even n
--   - encoding: gap Ω_r((log |T|)^(r/(r+1))) → a constant γ_r>0 chosen after r and before n and the history, with OPT(I)/MetricLP(I) ≥ γ_r(log |T|)^(r/(r+1)) in the success event; reason: this is the definition of Ω_r with constants depending only on r (p.5); the full exponent is retained
--   - generalization: with high probability (probability 1 − o(1)) → failure at most A_r_fail(log n)²/n² for a constant A_r_fail>0 depending only on r; reason: an explicit vanishing failure bound is stronger than 1 − o(1) and implies it; Appendix A.1 (C_F(n⁻⁴+rn⁻⁸)), Claim 4.5 with Appendix A.2 (O_r(n⁻³log⁵n)) and Claim 5.1 (O_r(n⁻²log²n)) supply it
--   - encoding: the instance is defined on the connected-cloud event of §3 → connectedness, validity, exact terminal count and positive MetricLP are clauses of the success event; reason: the raw law is unchanged and the finite positive instance prevents meaningless division by zero
--   - encoding: finite multigraph instance with normalized source costs → the published generic instance with parallel objective weights summed after computing distances; reason: every retraction and LP objective is preserved; the common normalization N_r cancels in the ratio
-- source:
--   Konstantin Makarychev, STOC 2027 submission #1436 (October 2026), Theorem 3.1, p.7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1436.pdf#page=7; PDF SHA-256 c6f69cddcebf9bb51692e022b1f2a1c3ca49babeba005dc1d6ce05e954bea358.

import Mathlib
import Definitions.Def_BootstrapRecolorVerify_MetricGap_Supplement_Instance

namespace BootstrapRecolorVerify.MetricGap.Supplement

/-- Theorem 3.1 p.7: the specified Part I construction, at EVERY sufficiently
large even n. The constants depend only on fixed r. The success event includes
connectedness and a valid positive-LP instance, without conditioning the law.
The failure rate follows from pp.11,17--18 and Appendix A.1--A.2, p.29. -/
theorem theorem_3_1 :
    ∀ r : ℕ, 2 ≤ r → ∃ γ A : ℝ, 0 < γ ∧ 0 < A ∧
      ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → Even n →
        1 - A * (Real.log n) ^ 2 / (n : ℝ) ^ 2 ≤
          rawProbability (fun H : History n r => GapEvent γ H) := by sorry

end BootstrapRecolorVerify.MetricGap.Supplement
