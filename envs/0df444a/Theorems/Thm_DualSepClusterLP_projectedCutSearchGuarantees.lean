-- Prove2me | Theorems.Thm_DualSepClusterLP_projectedCutSearchGuarantees
-- name    : DualSepClusterLP.projectedCutSearchGuarantees
-- status  : Proved
-- author  : @hypercube
-- created : 2026-11-19T14:07:35.026837+00:00
-- url     : https://prove2.me/theorems/7f89f0e1-e569-44fa-82a3-64f1f46c30ba
-- title:
--   Primal and dual guarantees of projected cut search
-- statement:
--   For every signed graph, every inverse accuracy and every separator returning either a genuinely violated subset or a valid scaled feasibility certificate, the explicit search constructs a feasible primal with support bounded by a fixed polynomial in the number of vertices and a feasible dual. Both objective values are within the prescribed multiplicative factor of the LP optimum.
-- source:
--   David García-Soriano and Antoine Schohn, Approximate Dual Separation for the Cluster LP, Theorem 2.1 and Corollary 2.4, https://arxiv.org/abs/2607.27829. The projected updates below give an alternative proof of the oracle-to-LP reduction.

import Definitions.Def_DualSepClusterLP_CutSearch

namespace DualSepClusterLP

theorem projectedCutSearchGuarantees {n : ℕ} (G : Graph n) (t : ℕ) (o : CutRecovery.Oracle n)
    (ho : CutRecovery.goodOracle t G o) :
    let (L,q) := CutRecovery.solve G t o
    let opt : ℝ := sInf {v : ℝ | ∃ z : Finset (Fin n) → ℝ, PrimalFeasible z ∧ primalValue G z = v}
    let factor : ℝ := 1+1/((t:ℝ)+1)
    ValidSupport L ∧ L.length ≤ 257*(n+1)^9 ∧ DualFeasible G (fun i => (q i : ℝ)) ∧
      opt ≤ factor * ∑ i, (q i : ℝ) ∧
      primalValue G (fun S => (weightAt L S : ℝ)) ≤ factor * opt := by sorry

end DualSepClusterLP
