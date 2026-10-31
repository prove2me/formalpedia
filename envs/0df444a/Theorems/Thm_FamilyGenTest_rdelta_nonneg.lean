-- Prove2me | Theorems.Thm_FamilyGenTest_rdelta_nonneg
-- name    : FamilyGenTest.rdelta_nonneg
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:12:52.707537+00:00
-- url     : https://prove2.me/theorems/af9fa6f0-923b-49df-b5bc-990a38493d38
-- title:
--   Proof of Theorem 1 — $r_i^\delta\ge0$
-- statement:
--   If $r_i^1(0)\le\bar r_i^1(1)$ and $\bar r_i^0(1)\le r_i^0(0)$ for every person, the weak inequalities of Assumption 4, then
--   $$
--   r_i^\delta=r_i^0(0)+\bar r_i^1(1)-\bar r_i^0(1)-r_i^1(0)\ge0.
--   $$
--
--   This is what makes the quadratic (EC.1) concave.
--
--   Differences from the source:
--   - generalization: Assumption 4 in full, with Assumptions 1, 2, 3 and stationary, positive, bounded rewards → only $r_i^1(0)\le\bar r_i^1(1)$ and $\bar r_i^0(1)\le r_i^0(0)$; reason: the dropped conditions are not used, and every instance of the source satisfies the two kept inequalities
-- source:
--   Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694 (Jan 24 2023), Proof of Theorem 1, p.ec2

import Mathlib
import Definitions.Def_FamilyGenTest_Rewards

namespace FamilyGenTest

/-- Proof of Theorem 1 (Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694
(Jan 24 2023), p.ec2): "From Assumption 4 we know `rᵢ^δ ≥ 0`". -/
theorem rdelta_nonneg {I : Type*} (R : Rewards I) (hR : CensoredOrder R) (i : I) :
    0 ≤ rdelta R i := by sorry

end FamilyGenTest
