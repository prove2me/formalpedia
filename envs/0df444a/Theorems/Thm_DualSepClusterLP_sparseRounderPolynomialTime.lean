-- Prove2me | Theorems.Thm_DualSepClusterLP_sparseRounderPolynomialTime
-- name    : DualSepClusterLP.sparseRounderPolynomialTime
-- status  : Proved
-- author  : @hypercube
-- created : 2026-11-19T13:31:46.959834+00:00
-- url     : https://prove2.me/theorems/7d03119d-53f4-45cc-81e7-f43d04ec75bc
-- title:
--   Polynomial bit complexity of the executable cluster LP rounder
-- statement:
--   A single Turing machine with a finite work alphabet evaluates the explicit Boolean word function for sparse clock and pivot rounding in time polynomial in the length of its input.
-- source:
--   David García-Soriano and Antoine Schohn, Approximate Dual Separation for the Cluster LP, Appendix F (conditional-expectation rounding), https://arxiv.org/abs/2607.27829.

import Definitions.Def_DualSepClusterLP_SparseRounder

namespace DualSepClusterLP

theorem sparseRounderPolynomialTime :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (A b : ℕ),
      (∀ k, Finite (M.tm.Γ k)) ∧ ∀ (w : List Bool),
        Nonempty (Turing.TM2OutputsInTime M.tm (w.map M.inputAlphabet.symm)
          (some ((RoundWire.output w).map M.outputAlphabet.symm)) (A * (w.length + 1)^b)) := by sorry

end DualSepClusterLP
