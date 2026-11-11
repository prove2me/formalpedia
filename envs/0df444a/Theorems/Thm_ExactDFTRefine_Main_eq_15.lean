-- Prove2me | Theorems.Thm_ExactDFTRefine_Main_eq_15
-- name    : ExactDFTRefine.Main.eq_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:02:03.096567+00:00
-- url     : https://prove2.me/theorems/b12ff33f-2b50-42f0-ac9f-640b31b34f34
-- title:
--   §4, Eq. (15) — (1 − ε)^11640 + 2γ^11640 + 2η^11640 ≤ 1/(1 + 11640ε) + 2^{−23} + 2^{−290} < 1
-- statement:
--   With $\varepsilon = 27/10^{12}$, $\gamma = 99857/100000$ and $\eta = 9583/10000$:
--   $$\gamma^{97} \le \frac{544}{625}, \qquad \Big(\frac{544}{625}\Big)^5 \le \frac12, \qquad \eta^{40} \le \frac12, \qquad \gamma^{11640} \le 2^{-24}, \qquad \eta^{11640} \le 2^{-291},$$
--   Bernoulli's inequality $(1-\varepsilon)^v \le (1 + v\varepsilon)^{-1}$ holds for every $v$, and
--   $$(1-\varepsilon)^{11640} + 2\gamma^{11640} + 2\eta^{11640} \le \frac{1}{1 + 11640\varepsilon} + 2^{-23} + 2^{-290} < 1, \tag{15}$$
--   where the slack of the last inequality exceeds $195/10^9$. Combined with Proposition 3.2 and Eq. (11), this is the sufficient condition $(1-\varepsilon)^v + 2\gamma^v + 2\eta^v < 1$ at $v = 11640$.
--
--   Differences from the source:
--   - generalization: Bernoulli's inequality (1 − ε)^v ≤ (1 + vε)^−1 for the tensor power v ≥ 1 → ∀ v : ℕ, (1 − ε)^v ≤ (1 + vε)⁻¹; reason: also covers v = 0, where both sides are 1; the paper's use is the instance v = 11640
--   - reading: its slack exceeds 195/10^9 → 195/10^9 < 1 − (1/(1 + 11640ε) + 2^−23 + 2^−290); reason: the slack of a strict inequality a < 1 is 1 − a
-- source:
--   Yao, Liu, A Numerical Refinement of an Exact Discrete Fourier Transform Bound, arXiv:2611.01257v1, p. 5, proof of Proposition 4.2 (Eq. (15))

import Mathlib
import Definitions.Def_ExactDFTRefine_Main_Moments

namespace ExactDFTRefine.Main

/-- **§4, Eq. (15)**, p. 5 (proof of Proposition 4.2). `γ^97 ≤ 544/625`, `(544/625)^5 ≤ 1/2`,
`η^40 ≤ 1/2`; `γ^11640 ≤ 2^{-24}`, `η^11640 ≤ 2^{-291}`; Bernoulli: `(1 - ε)^v ≤ (1 + vε)^{-1}`;
`(1 - ε)^11640 + 2γ^11640 + 2η^11640 ≤ 1/(1 + 11640ε) + 2^{-23} + 2^{-290} < 1` (15), with slack
exceeding `195/10^9`. -/
theorem eq_15 :
    gam ^ 97 ≤ 544 / 625 ∧ ((544 : ℝ) / 625) ^ 5 ≤ 1 / 2 ∧ eta ^ 40 ≤ 1 / 2 ∧
    gam ^ 11640 ≤ (2 : ℝ) ^ (-24 : ℤ) ∧ eta ^ 11640 ≤ (2 : ℝ) ^ (-291 : ℤ) ∧
    (∀ v : ℕ, (1 - eps) ^ v ≤ (1 + (v : ℝ) * eps)⁻¹) ∧
    (1 - eps) ^ 11640 + 2 * gam ^ 11640 + 2 * eta ^ 11640 ≤
      1 / (1 + 11640 * eps) + (2 : ℝ) ^ (-23 : ℤ) + (2 : ℝ) ^ (-290 : ℤ) ∧
    1 / (1 + 11640 * eps) + (2 : ℝ) ^ (-23 : ℤ) + (2 : ℝ) ^ (-290 : ℤ) < 1 ∧
    (195 : ℝ) / 10 ^ 9 <
      1 - (1 / (1 + 11640 * eps) + (2 : ℝ) ^ (-23 : ℤ) + (2 : ℝ) ^ (-290 : ℤ)) := by sorry

end ExactDFTRefine.Main
