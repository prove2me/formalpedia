-- Prove2me | Theorems.Thm_CachonFisherInventory_LowerBound_eq5_charge_decomposition
-- name    : CachonFisherInventory.LowerBound.eq5_charge_decomposition
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T02:50:33.101154+00:00
-- url     : https://prove2.me/theorems/9048129c-3959-417e-9b3d-d520ffbb9863
-- title:
--   Equation (5): expected supplier and retailer charge decomposition
-- statement:
--   Consider the §3 model with N≥1 retailers, arbitrary positive integer batch parameters Q_r,Q_s, nonnegative integer lead times L_r,L_s, arbitrary bounded integer iid consumer demand with Pr(D=1)>0, and costs h_s>0, h_r≥0, p_r≥0. Let the physical system have a stationary feasible causal joint law of beginning state, current action, and current demand. Its initial state may be random. Feasibility includes eventual fulfillment of every finite demand prefix. Fix any integer R. Define Ḡ_r,G_p,G_r,G_s as in §5.1, using L_r+1 periods of demand and the strictly next residue point above R. Let IL_s and IP_i be pre-demand echelon inventory and retailer inventory positions, excluding unshipped orders; let C be the actual end-of-period cost of equation (3). Then
--   $$\mathbb E[C]=\mathbb E[G_s(IL_s,IP,R)]+\sum_{i=1}^N\mathbb E[G_r(IP_i,R)].$$
--   The supplier expectation integrates G_s−b(R) nonnegatively and restores its concrete finite lower bound b(R); actual and retailer costs have nonnegative expectations. Equality is in the extended reals, so +∞ is preserved. Specializing R to the printed R* gives equation (5). This supporting stationary identity does not restrict the main all-policy goal.
--
--   Differences from the source:
--   - encoding: N identical retailers and batch inventories → retailers indexed by Fin N, integer net inventories, natural batch counts and finite fixed-length pipelines; reason: these carriers preserve all source instances and prevent truncated backlog arithmetic
--   - encoding: p_r is a backorder cost rate without a displayed sign inequality → p_r is nonnegative, including zero; h_s>0 and h_r≥0 are retained; reason: nonnegativity is the cost-rate convention; no positive incremental holding or penalty restriction is introduced
--   - reading: expected per-period charges are equated over an infinite horizon → the supporting identity is for a stationary joint state/action/demand law; reason: this makes the stationary shift of retailer costs explicit without imposing stationarity on the goal
--   - generalization: equation (5) uses R* → equation (5) is stated for every fixed integer R; reason: the transfer terms cancel for every R and the statement specializes to the full printed equation
--   - encoding: expected costs and charges may be infinite → EReal expectations use nonnegative integrals and the explicit finite supplier-charge offset b(R); reason: this avoids the zero default of a nonintegrable real integral and imposes no finite-cost restriction
-- source:
--   Cachon and Fisher (2000), Supply Chain Inventory Management and the Value of Shared Information, Management Science 46(8), DOI 10.1287/mnsc.46.8.1032.12029, §5.1, equation (5), p. 1039 (PDF p. 8)

import Definitions.Def_CachonFisherInventory_LowerBound_Criteria

open MeasureTheory CachonFisherInventory.LowerBound

namespace CachonFisherInventory.LowerBound

theorem eq5_charge_decomposition
    (P : Parameters) (μ : Measure (PhysicalTrace P))
    (hμ : StationaryPhysicalLaw P μ) (R : ℤ) :
    nonnegExpectation μ (fun w => actualCost P (physicalState P w 1)) =
      lowerExpectation μ (chargeFloor P R) (fun w => physicalSupplierCharge P R w 0) +
        ∑ i, nonnegExpectation μ (fun w => physicalRetailerCharge P R w 0 i) := by sorry

end CachonFisherInventory.LowerBound
