-- Prove2me | Theorems.Thm_CachonFisherInventory_LowerBound_policy_cost_lower_bound
-- name    : CachonFisherInventory.LowerBound.policy_cost_lower_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T02:50:51.470597+00:00
-- url     : https://prove2.me/theorems/c98e09b7-8a6f-48e1-8b2b-ae601a8d5cdf
-- title:
--   Section 5.2: cost lower bound under every feasible information policy
-- statement:
--   For every instance of the §3 model, there is a largest integer R* satisfying Ḡ_r(R*+Q_r)≤Ḡ_r(R*). For that same R*, and every finite initial physical inventory and pipeline state s,
--   $$\inf_{\pi\ \mathrm{feasible}}\limsup_{T\to\infty}\frac{1}{T+1}\sum_{t=0}^{T}\mathbb E_\pi[C_t]\ \ge\ \underline C_s(s,R^*)+N C_r(R^*).$$
--   Here N≥1 identical retailers face independent, identically distributed consumer demands over retailers and time, with arbitrary probability law on {0,…,d̄} and Pr(D=1)>0. Batch sizes Q_r,Q_s are arbitrary positive integers; lead times L_r,L_s are arbitrary nonnegative integers; h_s>0, h_r≥0 and p_r≥0. Supply is uncapacitated, all demand is backlogged and eventually filled, shipments are nonnegative Q_r-batches, and supplier orders are nonnegative Q_s Q_r-unit lots. C_t is actual holding and backlog cost from equation (3), not defined by charges.
--
--   The comparison includes all nonanticipative randomized history-dependent policies using full pre-demand information, hence also policies with traditional information. There is no stationary-policy, finite-state, bounded-memory or finite-cost restriction. For the same initial echelon position, retailer positions and supplier pipeline, C̲_s is the infimum of limsup expected Cesàro G_s charges over the location-relaxed causal system: allocations β_i may be any integers, IP_i=IP_i^b+β_i Q_r and Σ_i IP_i≤IL_s. Supplier order lots, supplier lead time, demand law and eventual fulfillment are retained. C_r(R*) is exactly Q_r⁻¹ Σ_{c=1}^{Q_r}Ḡ_r(R*+c), the average of all residues, with coefficients 1 and N unchanged.
--
--   Existence of R* is a conclusion, not a premise or choice default. The h_r=0 counterexample recorded separately is deliberately in the theorem's domain; no corrected critical-point convention is substituted. This is a statement of the printed construction, including its implicit definedness claim.
--
--   Differences from the source:
--   - encoding: N identical retailers and batch inventories → retailers indexed by Fin N, integer net inventories, natural batch counts and finite fixed-length pipelines; reason: these carriers preserve all source instances and prevent truncated backlog arithmetic
--   - encoding: p_r is a backorder cost rate without a displayed sign inequality → p_r is nonnegative, including zero; h_s>0 and h_r≥0 are retained; reason: nonnegativity is the cost-rate convention; no positive incremental holding or penalty restriction is introduced
--   - reading: R* is described as the largest integer and then used in the bound → existence of an integer satisfying IsGreatest is asserted together with the complete bound; reason: definedness is part of the printed construction and fails on an allowed h_r=0 instance; no existence premise or default is permitted
--   - reading: min E[C] and expected per-period infinite-horizon charges → policy infima of limsup expected Cesàro costs, from each finite initial physical state; reason: this specifies the steady-state notation for all feasible policies without assuming convergence, stationarity, attainment or a vanishing terminal term
--   - encoding: nonanticipative feasible information policies → causal probability laws of full trajectories, with demand independent of the complete pre-demand history; reason: strategic measures include independent policy randomization and all history-dependent policies; restricted-information policies form a subclass
--   - encoding: location relaxation allows negative retailer orders → signed integer allocations with an explicit supplier pipeline and eventual covering of each demand prefix; reason: negative reallocations alter location feasibility; fixed downstream delay is immaterial to eventuality and remains in the charge formula
--   - encoding: expected physical costs and signed supplier charges → nonnegative integrals, finite supplier-charge lower shifts, EReal infima and limsups; reason: infinite values are retained without undefined integral or infimum defaults
-- source:
--   Cachon and Fisher (2000), Supply Chain Inventory Management and the Value of Shared Information, Management Science 46(8), DOI 10.1287/mnsc.46.8.1032.12029, §5.2, unnumbered lower-bound inequality between equations (5) and (6), p. 1040 (PDF p. 9); R* specification §5.1, p. 1039 (PDF p. 8)

import Definitions.Def_CachonFisherInventory_LowerBound_Criteria

open CachonFisherInventory.LowerBound

namespace CachonFisherInventory.LowerBound

theorem policy_cost_lower_bound
    (P : Parameters) :
    ∃ R : ℤ, PrintedCriticalPoint P R ∧ ∀ s : Stock P,
      supplierLowerValue P (relaxedInitial P s) R +
        ((P.N * retailerLowerValue P R : ℝ) : EReal) ≤ physicalValue P s := by sorry

end CachonFisherInventory.LowerBound
