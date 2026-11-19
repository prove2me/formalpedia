-- Prove2me | Theorems.Thm_DualSepClusterLP_deterministicRounding
-- name    : DualSepClusterLP.deterministicRounding
-- status  : Open
-- author  : @hypercube
-- created : 2026-11-18T17:42:49.929855+00:00
-- url     : https://prove2.me/theorems/19377695-09df-4953-95d1-511d49403435
-- title:
--   Theorem 1.3 — deterministic cluster-LP rounding at $1.3865$
-- statement:
--   From an explicitly represented feasible rational cluster-LP solution, a deterministic polynomial-time algorithm returns a clustering with cost at most $2773/2000$ times the supplied objective value.
-- source:
--   David García-Soriano and Antoine Schohn, Approximate Dual Separation for the Cluster LP, STOC 2027 paper #79, §1, Theorem 1.3 and Appendix F, Proposition F.1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/79.pdf

import Mathlib
import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_DualSepClusterLP_SparseInput

namespace DualSepClusterLP

/-- Theorem 1.3 and Proposition F.1 for an explicitly supplied feasible rational support.
The step bound is polynomial in the full bit length of the graph and LP input. -/
theorem deterministicRounding :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (A b : ℕ),
      (∀ k, Finite (M.tm.Γ k)) ∧
      ∀ (n : ℕ) (G : Graph n) (L : SparseWeights n), ValidSupport L →
        ∃ C : Clustering n,
          Nonempty (Turing.TM2OutputsInTime M.tm
            ((roundingInput G L).map M.inputAlphabet.symm)
            (some ((partitionOutput C).map M.outputAlphabet.symm))
            (A * ((roundingInput G L).length + 1)^b)) ∧
          (disagreements G C : ℝ) ≤ (2773 / 2000 : ℝ) *
            primalValue G (fun S => (weightAt L S : ℝ)) := by sorry

end DualSepClusterLP
