-- Prove2me | Theorems.Thm_DualSepClusterLP_primalDualApproximation
-- name    : DualSepClusterLP.primalDualApproximation
-- status  : Proved
-- author  : @hypercube
-- created : 2026-11-18T17:42:10.461318+00:00
-- url     : https://prove2.me/theorems/d21cc7b8-e1a2-41cd-a24f-85b88e3ecb75
-- title:
--   Corollary 2.4 — sparse primal and dual solutions for the cluster LP
-- statement:
--   The deterministic solver returns exactly feasible signed rational prices and an explicitly supported feasible rational primal vector. At accuracy $\varepsilon$ their objectives bound the fractional optimum from below and above within a factor $1+\varepsilon$ on each side. The support is polynomial in $n$ and the running time is $2^{\mathrm{poly}(1/\varepsilon)}\mathrm{poly}(n)$.
-- source:
--   David García-Soriano and Antoine Schohn, Approximate Dual Separation for the Cluster LP, STOC 2027 paper #79, §2, Corollary 2.4 (LP optimization conclusion of Theorem 1.1). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/79.pdf

import Mathlib
import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_DualSepClusterLP_SparseInput

namespace DualSepClusterLP

/-- Corollary 2.4 at accuracy 1/(t+1). The LP optimum is the infimum of the
objectives of all feasible real primal vectors. The output contains the explicit
rational primal list, followed by the signed rational dual prices. -/
theorem primalDualApproximation :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (A a b D d : ℕ),
      (∀ k, Finite (M.tm.Γ k)) ∧
      ∀ (t n : ℕ) (G : Graph n), ∃ (L : SparseWeights n) (q : Fin n → ℚ),
        Nonempty (Turing.TM2OutputsInTime M.tm
          ((graphInput t G).map M.inputAlphabet.symm)
          (some ((roundingInput G L ++ pricesBits q).map M.outputAlphabet.symm))
          (2 ^ (A * (t+1)^a) * (n+1)^b)) ∧
        ValidSupport L ∧ L.length ≤ D * (n+1)^d ∧
        DualFeasible G (fun i => (q i : ℝ)) ∧
        let opt : ℝ := sInf {v : ℝ | ∃ z : Finset (Fin n) → ℝ, PrimalFeasible z ∧ primalValue G z = v}
        let factor : ℝ := 1 + 1 / ((t : ℝ) + 1)
        opt ≤ factor * ∑ i : Fin n, (q i : ℝ) ∧
          primalValue G (fun S => (weightAt L S : ℝ)) ≤ factor * opt := by sorry

end DualSepClusterLP
