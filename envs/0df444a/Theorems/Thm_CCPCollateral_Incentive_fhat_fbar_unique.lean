-- Prove2me | Theorems.Thm_CCPCollateral_Incentive_fhat_fbar_unique
-- name    : CCPCollateral.Incentive.fhat_fbar_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:15.38574+00:00
-- url     : https://prove2.me/theorems/e4a16526-2b65-4bdc-a68d-b894cc5b0f9f
-- title:
--   Proof of Proposition 2, Step 1, p. 45 — F̂(I), F̄(I) uniquely determined by (18), (A3); 0 ≤ F̂ < F̄ < D − I; both continuous
-- statement:
--   Under the standing assumptions, let $\hat I(0)$ be the least initial margin at which hedging is incentive compatible with $F=0$ when all other members hedge. For every $I\in[0,\hat I(0)]$:
--   1. equation (18), $D-I-F+X^{N-1}(I,F)=(A_{CCP}-I-F)\mathcal P$, has exactly one root $F\in[0,D-I)$, and it is $\hat F(I)$;
--   2. equation (A3), $D-I-F+X^{0}(I,F)=(A_{CCP}-I-F)\mathcal P$, has exactly one root $F\in[0,D-I)$, and it is $\bar F(I)$;
--   3. $0\le\hat F(I)<\bar F(I)<D-I$.
--
--   Moreover $\hat F$ and $\bar F$ are continuous on $[0,\hat I(0)]$.
--
--   Here $\hat F(I)$ ($\bar F(I)$) is the least default fund that makes hedging a best response when all (no) other members hedge. The interval $[\hat F(I),\bar F(I)]$ is the region of multiple equilibria in Step 1 of the proof of Proposition 2.
--
--   **Formalization Note** $\hat F$, $\bar F$ and $\hat I(0)$ are defined as least incentive-compatible values (infima), not as roots of (18) and (A3); that they solve these equations is part of the statement.
-- source:
--   Wang, Capponi & Zhang, A Theory of Collateral Requirements for Central Counterparties, author's manuscript (2021; Management Sci. doi:10.1287/mnsc.2021.4145), proof of Proposition 2, Step 1, (A3) and the paragraph after it, p. 45

import Mathlib
import Definitions.Def_CCPCollateral_Incentive_Setting

namespace CCPCollateral.Incentive

/-- Proof of Proposition 2, Step 1 (p. 45): for `I ∈ [0, Î(0)]`, (18) and (A3) each have exactly
one root `F ∈ [0, D − I)`, namely `F̂(I)` and `F̄(I)`; `0 ≤ F̂(I) < F̄(I) < D − I`; and `F̂`, `F̄` are
continuous in `I`. -/
theorem fhat_fbar_unique (m : Params) (hm : Standing m) :
    (∀ I ∈ Set.Icc 0 m.Ihat0,
      (∃! F, 0 ≤ F ∧ F < m.D - I ∧ m.Eq18 I F) ∧
      (∃! F, 0 ≤ F ∧ F < m.D - I ∧ m.EqA3 I F) ∧
      m.Eq18 I (m.Fhat I) ∧ m.EqA3 I (m.Fbar I) ∧
      0 ≤ m.Fhat I ∧ m.Fhat I < m.Fbar I ∧ m.Fbar I < m.D - I) ∧
    ContinuousOn m.Fhat (Set.Icc 0 m.Ihat0) ∧
    ContinuousOn m.Fbar (Set.Icc 0 m.Ihat0) := by sorry

end CCPCollateral.Incentive
