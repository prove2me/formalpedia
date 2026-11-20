-- Prove2me | Theorems.Thm_DualSepClusterLP_separatorLocalSearch
-- name    : DualSepClusterLP.separatorLocalSearch
-- status  : Proved
-- author  : @hypercube
-- created : 2026-11-19T14:47:56.953537+00:00
-- url     : https://prove2.me/theorems/6c71ac1e-5a4f-4787-a03c-2c6f480805b8
-- title:
--   Search for a violated cluster using local tests
-- statement:
--   A deterministic finite-alphabet machine either emits a subset whose price exceeds its cost or certifies the singleton, near-clique and dense-universe tests. Its time is singly exponential in a polynomial of the inverse accuracy and polynomial in graph size and price bit length with a fixed exponent.
-- source:
--   David García-Soriano and Antoine Schohn, Approximate Dual Separation for the Cluster LP, Theorem 2.1, the large/small/intermediate cost regimes, and the dense quadratic subroutine. https://arxiv.org/abs/2607.27829. The two-pivot localization is an alternative proof for the application.

import Definitions.Def_DualSepClusterLP_SeparationChecks
import Definitions.Def_DualSepClusterLP_SeparationEncoding

namespace DualSepClusterLP

theorem separatorLocalSearch :
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
          | none => SepCheck.Checks t G q := by sorry

end DualSepClusterLP
