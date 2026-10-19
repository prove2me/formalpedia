-- Prove2me | Theorems.Thm_CrossLicensing_Innovation_interior_solution
-- name    : CrossLicensing.Innovation.interior_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T13:01:29.230101+00:00
-- url     : https://prove2.me/theorems/6faa802d-2857-4b6c-8cf9-c937a9fcec3d
-- title:
--   Proof of Proposition 2, p. A.1 — T^I_i is the unique joint solution of both manufacturers' duopoly first-order conditions
-- statement:
--   Assume $0 \le \beta \le 1$, $49/144 < k_2 < k_1$ and $\hat k_2(k_1\mid\beta) \le k_2$. With the duopoly gross profits of Lemma 1,
--   $$\Pi^d_1(T_1,T_2) = \tfrac1{144}((5\beta-7)T_1 + (5-7\beta)T_2 - 2)^2,\qquad \Pi^d_2(T_1,T_2) = \tfrac1{144}((5\beta-7)T_2 + (5-7\beta)T_1 - 2)^2,$$
--   the denominators of $T^I_1$ and $T^I_2$ are nonzero, and for all real $T_1, T_2$ the pair of first-order conditions
--   $$\frac{\partial}{\partial T_1}\big[\Pi^d_1(T_1,T_2) - k_1T_1^2\big] = 0,\qquad \frac{\partial}{\partial T_2}\big[\Pi^d_2(T_1,T_2) - k_2T_2^2\big] = 0$$
--   holds if and only if $(T_1, T_2) = (T^I_1, T^I_2)$, where
--   $$T^I_i = \frac{(5\beta-7)(-5\beta^2 + 12\beta + 12k_j - 7)}{6k_j((7-5\beta)^2 - 144k_i) + (7-5\beta)^2(\beta^2 + 6k_i - 1)}.$$
--
--   This identifies the paper's interior duopoly candidate.
--
--   **Formalization Note** The first-order conditions are stated as derivatives of the explicit duopoly polynomials (`HasDerivAt … 0`). The hypothesis $\hat k_2 \le k_2$ is where the paper uses $T^I$; for smaller $k_2$ the linear system can degenerate.
-- source:
--   Wang, Huang, Lee, Cross-licensing in a Supply Chain with Asymmetric Manufacturers, SSRN 3053682 (version of 2023-04-27), proof of Proposition 2, p. A.1 (PDF 33)

import Mathlib
import Definitions.Def_CrossLicensing_Innovation_Model
import Definitions.Def_CrossLicensing_Innovation_ClosedForms

namespace CrossLicensing.Innovation

theorem interior_solution (β k1 k2 : ℝ) (h : Standing β k1 k2) (hk : khat2 β k1 ≤ k2) :
    6 * k2 * ((7 - 5 * β) ^ 2 - 144 * k1) + (7 - 5 * β) ^ 2 * (β ^ 2 + 6 * k1 - 1) ≠ 0 ∧
    6 * k1 * ((7 - 5 * β) ^ 2 - 144 * k2) + (7 - 5 * β) ^ 2 * (β ^ 2 + 6 * k2 - 1) ≠ 0 ∧
    ∀ T1 T2 : ℝ,
      (HasDerivAt (fun x => duoGross1 β x T2 - k1 * x ^ 2) 0 T1 ∧
        HasDerivAt (fun x => duoGross2 β T1 x - k2 * x ^ 2) 0 T2) ↔
      (T1 = TI1 β k1 k2 ∧ T2 = TI2 β k1 k2) := by sorry

end CrossLicensing.Innovation
