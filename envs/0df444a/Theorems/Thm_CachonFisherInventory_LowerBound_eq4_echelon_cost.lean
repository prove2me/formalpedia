-- Prove2me | Theorems.Thm_CachonFisherInventory_LowerBound_eq4_echelon_cost
-- name    : CachonFisherInventory.LowerBound.eq4_echelon_cost
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T02:48:41.726038+00:00
-- url     : https://prove2.me/theorems/eda9601b-0467-46a1-9895-942142e51263
-- title:
--   Equation (4): echelon inventory cost identity
-- statement:
--   For the §3 supply-chain parameters and any end-of-period physical state, let I_s be supplier on-hand stock in batches, and let I_i, B_i and IT_i be retailer on-hand stock, backlogs and in-transit stock in units. Net inventory is I_i−B_i; I_i and B_i are its positive and negative parts. Let IL_s^e=Q_r I_s+Σ_i(IT_i+I_i−B_i). With actual cost C defined independently by equation (3),
--   $$C=h_s IL_s^e+\sum_{i=1}^N[h_r I_i+(h_s+p_r)B_i].$$
--   This identity is pathwise; it makes no stationarity or probability assumption on the state. Supplier and retailer order pipelines do not alter this algebraic identity.
--
--   Differences from the source:
--   - encoding: N identical retailers and batch inventories → retailers indexed by Fin N, integer net inventories, natural batch counts and finite fixed-length pipelines; reason: these carriers preserve all source instances and prevent truncated backlog arithmetic
--   - encoding: p_r is a backorder cost rate without a displayed sign inequality → p_r is nonnegative, including zero; h_s>0 and h_r≥0 are retained; reason: nonnegativity is the cost-rate convention; no positive incremental holding or penalty restriction is introduced
-- source:
--   Cachon and Fisher (2000), Supply Chain Inventory Management and the Value of Shared Information, Management Science 46(8), DOI 10.1287/mnsc.46.8.1032.12029, §5.1, equation (4), p. 1039 (PDF p. 8)

import Definitions.Def_CachonFisherInventory_LowerBound_Physical

open CachonFisherInventory.LowerBound

namespace CachonFisherInventory.LowerBound

theorem eq4_echelon_cost
    (P : Parameters) (s : Stock P) :
    actualCost P s = P.hs * (echelon P s : ℝ) +
      ∑ i, (P.hr * onHand s i + (P.hs + P.pr) * backlog s i) := by sorry

end CachonFisherInventory.LowerBound
