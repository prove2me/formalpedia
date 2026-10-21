-- Prove2me | Theorems.Thm_CCPCollateral_Incentive_eq_A15_A17
-- name    : CCPCollateral.Incentive.eq_A15_A17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:14.713302+00:00
-- url     : https://prove2.me/theorems/49537414-ee9b-47ba-95b3-a07a6fa1adb8
-- title:
--   (A15), (A17), proof of Proposition 2, p. 48 — explicit F̂(I) with l = ⌈N F̂/(D − I)⌉, and explicit Î(0)
-- statement:
--   Under the standing assumptions, let $y_l^{(N)}(q_s)=\sum_{k=l}^{N-1}\binom{N-1}{k}q_s^k(1-q_s)^{N-1-k}\frac{N}{N-k}$ and $z_l^{(N)}(q_s)=\sum_{k=l}^{N-1}\binom{N-1}{k}q_s^k(1-q_s)^{N-1-k}$ as in (A13)–(A14).
--   1. For every $I\in[0,\hat I(0)]$, with $l=\lceil N\hat F(I)/(D-I)\rceil$,
--   $$\hat F(I)=D-I-\frac{(A_{CCP}-D)\mathcal P+\alpha z_l^{(N)}(q_s)(D-I)}{\frac{1-q_s^N}{1-q_s}-\mathcal P+\alpha y_l^{(N)}(q_s)}.\qquad\text{(A15)}$$
--   2. $$\hat I(0)=D-\frac{(A_{CCP}-D)\mathcal P}{(1+\alpha)\frac{q_s-q_s^N}{1-q_s}+1-\mathcal P}.\qquad\text{(A17)}$$
--
--   (A16), the value $\hat F(0)$, is (A15) at $I=0$. These formulas make the piecewise-linear cutoff explicit.
--
--   **Formalization Note** $\lceil\cdot\rceil$ is the natural-number ceiling, which agrees with the integer ceiling since $N\hat F(I)/(D-I)\ge 0$.
-- source:
--   Wang, Capponi & Zhang, A Theory of Collateral Requirements for Central Counterparties, author's manuscript (2021; Management Sci. doi:10.1287/mnsc.2021.4145), proof of Proposition 2, Step 3, (A13)–(A17), p. 48

import Mathlib
import Definitions.Def_CCPCollateral_Incentive_Setting

namespace CCPCollateral.Incentive

/-- (A15) and (A17), proof of Proposition 2, Step 3 (p. 48): with `l = ⌈N F̂(I)/(D − I)⌉`,
`F̂(I) = D − I − ((A_CCP − D)𝒫 + α z_l (D − I)) / ((1 − q_s^N)/(1 − q_s) − 𝒫 + α y_l)` on
`[0, Î(0)]`, and `Î(0) = D − (A_CCP − D)𝒫 / ((1 + α)(q_s − q_s^N)/(1 − q_s) + 1 − 𝒫)`. -/
theorem eq_A15_A17 (m : Params) (hm : Standing m) :
    (∀ I ∈ Set.Icc 0 m.Ihat0,
      m.Fhat I = m.D - I -
        ((m.Accp - m.D) * m.pledge + m.α * m.z ⌈(m.N : ℝ) * m.Fhat I / (m.D - I)⌉₊ * (m.D - I)) /
          ((1 - m.qs ^ m.N) / (1 - m.qs) - m.pledge +
            m.α * m.y ⌈(m.N : ℝ) * m.Fhat I / (m.D - I)⌉₊)) ∧
    m.Ihat0 = m.D - (m.Accp - m.D) * m.pledge /
      ((1 + m.α) * (m.qs - m.qs ^ m.N) / (1 - m.qs) + 1 - m.pledge) := by sorry

end CCPCollateral.Incentive
