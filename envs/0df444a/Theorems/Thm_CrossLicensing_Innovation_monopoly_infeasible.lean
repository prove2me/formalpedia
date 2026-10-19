-- Prove2me | Theorems.Thm_CrossLicensing_Innovation_monopoly_infeasible
-- name    : CrossLicensing.Innovation.monopoly_infeasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T13:01:24.656053+00:00
-- url     : https://prove2.me/theorems/dfd36be7-d945-4a32-90e4-5b7c35b46356
-- title:
--   Proof of Proposition 2, p. A.1 — M2's monopoly investment T^m_2 = 1/(16k2 − 1) lies below T̂2(0|β): no monopoly
-- statement:
--   Let $k_2 > 49/144$ and $0 \le \beta < \sqrt3 - 1$. Consider manufacturer 2's payoff as a monopolist when $T_1 = 0$, namely its monopoly gross profit $\tfrac1{16}(T_2 + 1)^2$ (Lemma 1 at $T_1 = 0$) minus its investment $k_2T_2^2$. Then $T^m_2 = 1/(16k_2 - 1)$ is nonnegative and is the unique maximizer of
--   $$T_2 \mapsto \tfrac1{16}(T_2+1)^2 - k_2T_2^2 \quad\text{over } T_2 \ge 0,$$
--   and it lies strictly below the duopoly boundary:
--   $$T^m_2 = \frac{1}{16k_2 - 1} < \hat T_2(0\mid\beta) = \frac{2 - \sqrt3}{\sqrt3 - 1 - \beta}.$$
--
--   Since Lemma 1 requires $T_2 > \hat T_2(0\mid\beta)$ for the supplier to choose a monopoly, manufacturer 2's own monopoly optimum never reaches the monopoly region: this is the paper's argument that a monopoly is not an equilibrium outcome.
--
--   **Formalization Note** The paper argues at $T_1 = 0$ only, as stated here; the claim for every profile is part of the goal theorem (every innovation equilibrium is a duopoly).
-- source:
--   Wang, Huang, Lee, Cross-licensing in a Supply Chain with Asymmetric Manufacturers, SSRN 3053682 (version of 2023-04-27), proof of Proposition 2, p. A.1 (PDF 33)

import Mathlib
import Definitions.Def_CrossLicensing_Innovation_ClosedForms

namespace CrossLicensing.Innovation

theorem monopoly_infeasible (β k2 : ℝ) (hk2 : 49 / 144 < k2) (hβ0 : 0 ≤ β)
    (hβ : β < Real.sqrt 3 - 1) :
    0 ≤ 1 / (16 * k2 - 1) ∧
    (∀ T2 : ℝ, 0 ≤ T2 → T2 ≠ 1 / (16 * k2 - 1) →
      (T2 + 1) ^ 2 / 16 - k2 * T2 ^ 2 <
        (1 / (16 * k2 - 1) + 1) ^ 2 / 16 - k2 * (1 / (16 * k2 - 1)) ^ 2) ∧
    1 / (16 * k2 - 1) < That2 β 0 := by sorry

end CrossLicensing.Innovation
