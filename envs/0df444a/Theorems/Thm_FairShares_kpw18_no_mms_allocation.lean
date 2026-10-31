-- Prove2me | Theorems.Thm_FairShares_kpw18_no_mms_allocation
-- name    : FairShares.kpw18_no_mms_allocation
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:12:34.505148+00:00
-- url     : https://prove2.me/theorems/0ec4f6a4-3f3a-4fdc-92fe-cf56efab13d9
-- title:
--   [KPW18]: three additive agents with no MMS allocation
-- statement:
--   There are a number $m$ of goods and three additive valuations $v_1,v_2,v_3$ on them such that no allocation $(A_1,A_2,A_3)$ gives every agent her maximin share:
--   $$
--   \neg\,\exists A\ \ \forall i\in\{1,2,3\}:\ v_i(A_i)\ge \mathrm{MMS}_3(v_i).
--   $$
--
--   The paper cites this from Kurokawa, Procaccia and Wang (J. ACM, 2018) and does not prove it; it is the last step of the proof of Theorem 1.
--
--   Differences from the source:
--   - reading: "there are instances" (p.16) with the instance of [KPW18] for three agents (p.13) → an instance with exactly n = 3 agents and some number m of goods; reason: p.13 names the [KPW18] instance as one with three agents; fixing n = 3 is the stronger of the two readings
--   - encoding: MMSₙ(v), Definition 1 → the published LittleCharity.MMS.mms v 3 Finset.univ; reason: Definition 1 for n = 3
--   - encoding: an allocation (partition into n possibly empty bundles) → A : Fin m → Fin 3, agent i's bundle A⁻¹(i); reason: maps to Fin 3 are exactly the labelled partitions into three possibly empty bundles
-- source:
--   Babaioff & Feige, Fair Shares: Feasibility, Domination and Incentives, arXiv:2205.07519v1, proof of Theorem 1, p.16 ("Yet, for agents with additive valuations, there are instances for which no allocation gives each agent her MMS [KPW18]."); §3.3, p.13 (three agents)

import Mathlib
import Definitions.Def_FairShares_IsAdditive
import Definitions.Def_FairShares_bundle
import Definitions.Def_LittleCharity_MMS_Setting

namespace FairShares

/-- **[KPW18]: an additive instance with three agents admits no MMS allocation.**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*, arXiv:2205.07519v1, proof of Theorem 1, p.16: "Yet, for agents with additive valuations, there are instances
for which no allocation gives each agent her MMS [KPW18]." and §3.3, p.13: "the instance I
presented in [KPW18] for three agents with valuations denoted by (v1, v2, v3), for which it is not
possible to give every agent her MMS".

There are a number `m` of items and three additive valuations `v₀, v₁, v₂` on the bundles of
`Fin m` such that no allocation `A : Fin m → Fin 3` gives every agent `i` a bundle worth at least
`MMS_3(v_i)`.

**Formalization Note.** `MMS_3(v)` is the published `LittleCharity.MMS.mms v 3 Finset.univ`.
The instance is external to the paper (Kurokawa, Procaccia, Wang, J. ACM 65(2), 2018); `m` is
left existential. -/
theorem kpw18_no_mms_allocation :
    ∃ m : ℕ, ∃ vs : Fin 3 → (Finset (Fin m) → ℝ), (∀ i, IsAdditive (vs i)) ∧
      ¬ ∃ A : Fin m → Fin 3, ∀ i, LittleCharity.MMS.mms (vs i) 3 Finset.univ ≤ vs i (bundle A i) := by sorry

end FairShares
