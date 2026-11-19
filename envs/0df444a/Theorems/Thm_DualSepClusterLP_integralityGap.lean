-- Prove2me | Theorems.Thm_DualSepClusterLP_integralityGap
-- name    : DualSepClusterLP.integralityGap
-- status  : Open
-- author  : @hypercube
-- created : 2026-11-18T17:43:10.618193+00:00
-- url     : https://prove2.me/theorems/14438be2-13a3-46de-8191-3ea54c29b2d8
-- title:
--   Integrality-gap consequence of Theorem 1.3
-- statement:
--   Every feasible real solution of the cluster LP admits a partition of disagreement cost at most $2773/2000$ times its fractional objective value.
-- source:
--   David García-Soriano and Antoine Schohn, Approximate Dual Separation for the Cluster LP, STOC 2027 paper #79, §1, consequence immediately following Theorem 1.3, printed p. 3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/79.pdf

import Mathlib
import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_DualSepClusterLP_LinearProgram

namespace DualSepClusterLP

/-- The integrality-gap consequence of Theorem 1.3 (page 3). -/
theorem integralityGap {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (hz : PrimalFeasible z) :
    ∃ C : Clustering n, (disagreements G C : ℝ) ≤ (13865 / 10000 : ℝ) * primalValue G z := by sorry

end DualSepClusterLP
