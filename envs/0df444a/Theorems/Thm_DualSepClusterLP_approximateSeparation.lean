-- Prove2me | Theorems.Thm_DualSepClusterLP_approximateSeparation
-- name    : DualSepClusterLP.approximateSeparation
-- status  : Open
-- author  : @hypercube
-- created : 2026-11-18T17:41:29.449226+00:00
-- url     : https://prove2.me/theorems/782708a0-6dcc-4a05-ab2c-7dd0e9dd0956
-- title:
--   Theorem 2.1 — deterministic approximate dual separation
-- statement:
--   For each accuracy the algorithm either exhibits a subset that violates the original dual inequality or certifies dual feasibility after dividing the prices by one plus the requested error. Its running time is singly exponential in a polynomial of inverse accuracy and polynomial in the graph size and price bit length.
-- source:
--   David García-Soriano and Antoine Schohn, Approximate Dual Separation for the Cluster LP, STOC 2027 paper #79, §2, Theorem 2.1 (also Theorem 1.1). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/79.pdf

import Mathlib
import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_DualSepClusterLP_LinearProgram
import Definitions.Def_DualSepClusterLP_SeparationEncoding

namespace DualSepClusterLP

/-- Theorem 2.1 at accuracy 1/(t+1). A genuine violation and scaled feasibility can both hold.
The machine may return either answer whenever its stated condition holds. -/
theorem approximateSeparation :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (A a b : ℕ),
      (∀ k, Finite (M.tm.Γ k)) ∧
      ∀ (t n : ℕ) (G : Graph n) (q : Fin n → ℚ),
        ∃ result : Option (Finset (Fin n)),
          Nonempty (Turing.TM2OutputsInTime M.tm
            ((separationInput t G q).map M.inputAlphabet.symm)
            (some ((separationOutput result).map M.outputAlphabet.symm))
            (2 ^ (A * (t+1)^a) * (n+(pricesBits q).length+1)^b)) ∧
          match result with
          | some S => subsetCost G S < ∑ i ∈ S, (q i : ℝ)
          | none => DualFeasible G (fun i => (q i : ℝ) / (1 + 1 / ((t : ℝ) + 1))) := by sorry

end DualSepClusterLP
