-- Prove2me | Theorems.Thm_ActuarialValuation_pucFutureNormalCost_succ
-- name    : ActuarialValuation.pucFutureNormalCost_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:06:05.55272+00:00
-- url     : https://prove2.me/theorems/10172739-535c-47ce-a22c-fc14a3dd8906
-- title:
--   Actuarial liability and normal cost: pucFutureNormalCost_succ
-- statement:
--   The actuarial normal cost of an extra future service year adds exactly its retirement value. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   PVFNC_{m+1}=PVFNC_m+NC_{n+m}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. American Academy of Actuaries, Fundamentals of Pension Accounting and Funding (2004), https://www.actuary.org/sites/default/files/pdf/pension/fundamentals_0704.pdf; IFoA GN26 Pension Fund Terminology (2006), https://www.actuaries.org.uk/system/files/documents/pdf/gn26v2-1.pdf; IMF, Conducting Stress Tests of Defined Benefit Pension Plans (2014), https://www.elibrary.imf.org/display/book/9781484368589/ch012.xml. Parent topic: Projected unit credit pension funding, service attribution, normal cost, actuarial liability and amortisation of unfunded pension liabilities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuary.org/sites/default/files/pdf/pension/fundamentals_0704.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucNormalCost
import Definitions.Def_actuarial_pucFutureNormalCost

namespace ActuarialValuation

theorem pucFutureNormalCost_succ (u : ℕ → ℝ) (n m : ℕ) (f : ℝ) : pucFutureNormalCost u n (m+1) f = pucFutureNormalCost u n m f + pucNormalCost u (n+m) f := by sorry

end ActuarialValuation
