-- Prove2me | Theorems.Thm_CCPCollateral_Incentive_eq_A8_kinks
-- name    : CCPCollateral.Incentive.eq_A8_kinks
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:27.34847+00:00
-- url     : https://prove2.me/theorems/59e652e0-8392-46b7-aad2-508489fd2c78
-- title:
--   (A8), proof of Proposition 2, pp. 46–47 — each kink I_l is unique, satisfies (A8), and I_l > I_{l+1}
-- statement:
--   Under the standing assumptions, the kinks of $\hat F$ are the points $I_l\in[0,\hat I(0)]$ with $N\hat F(I_l)=l(D-I_l)$.
--   1. For every $l=0,1,\dots,\lceil N\hat F(0)/D\rceil-1$ there is exactly one such $I_l$.
--   2. Every kink satisfies (A8):
--   $$\left(\frac{1-q_s^N}{1-q_s}-\mathcal P\right)\bigl(D-I_l-\hat F(I_l)\bigr)+\alpha\,\mathbb E^s\!\left[\frac{\bigl(\mathcal N_d(D-I_l)-N\hat F(I_l)\bigr)^+}{N-\mathcal N_d}\right]=(A_{CCP}-D)\,\mathcal P.$$
--   3. If $I_l$ and $I_{l+1}$ are kinks for $l$ and $l+1$, then $I_{l+1}<I_l$.
--
--   The kinks thus form a decreasing sequence, and between consecutive kinks the integer $\lceil N\hat F(I)/(D-I)\rceil$ is constant.
--
--   **Formalization Note** $\mathbb E^s$ is the finite sum against $f^{N-1}$.
-- source:
--   Wang, Capponi & Zhang, A Theory of Collateral Requirements for Central Counterparties, author's manuscript (2021; Management Sci. doi:10.1287/mnsc.2021.4145), proof of Proposition 2, Step 2, (A8) and the following paragraph, pp. 46–47

import Mathlib
import Definitions.Def_CCPCollateral_Incentive_Setting

namespace CCPCollateral.Incentive

/-- (A8) and `I_l > I_{l+1}`, proof of Proposition 2, Step 2 (pp. 46–47): for each
`l = 0, 1, …, ⌈N F̂(0)/D⌉ − 1` there is exactly one `I_l ∈ [0, Î(0)]` with
`N F̂(I_l) = l (D − I_l)`; every such kink satisfies (A8); and `I_{l+1} < I_l`. -/
theorem eq_A8_kinks (m : Params) (hm : Standing m) :
    (∀ l : ℕ, (l : ℤ) < ⌈(m.N : ℝ) * m.Fhat 0 / m.D⌉ →
      ∃! I, I ∈ Set.Icc 0 m.Ihat0 ∧ (m.N : ℝ) * m.Fhat I = l * (m.D - I)) ∧
    (∀ l : ℕ, ∀ I ∈ Set.Icc 0 m.Ihat0, (m.N : ℝ) * m.Fhat I = l * (m.D - I) →
      ((1 - m.qs ^ m.N) / (1 - m.qs) - m.pledge) * (m.D - I - m.Fhat I) +
          m.α * ∑ k ∈ Finset.range m.N, m.defaultLaw (m.N - 1) k *
            (max ((k : ℝ) * (m.D - I) - m.N * m.Fhat I) 0 / ((m.N : ℝ) - k)) =
        (m.Accp - m.D) * m.pledge) ∧
    (∀ l : ℕ, ∀ I ∈ Set.Icc 0 m.Ihat0, ∀ J ∈ Set.Icc 0 m.Ihat0,
      (m.N : ℝ) * m.Fhat I = l * (m.D - I) →
      (m.N : ℝ) * m.Fhat J = ((l : ℝ) + 1) * (m.D - J) → J < I) := by sorry

end CCPCollateral.Incentive
