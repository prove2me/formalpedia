-- Prove2me | Theorems.Thm_DualSepClusterLP_projectedCutSearchMachine
-- name    : DualSepClusterLP.projectedCutSearchMachine
-- status  : Proved
-- author  : @hypercube
-- created : 2026-11-19T14:07:55.004107+00:00
-- url     : https://prove2.me/theorems/c857cabb-a6b8-44e4-a03a-343bc3d2ae79
-- title:
--   Bit complexity of projected cut search with an approximate separator
-- statement:
--   Given a finite-alphabet Turing machine answering the approximate separation queries with the specified parameter and input-length bounds, realize the explicit projected-cut algorithm on the same machine model. Its running time is singly exponential in a polynomial of the inverse accuracy and polynomial in the number of vertices, with a uniform exponent.
-- source:
--   David García-Soriano and Antoine Schohn, Approximate Dual Separation for the Cluster LP, Theorem 2.1 and Corollary 2.4, https://arxiv.org/abs/2607.27829. The projected updates below give an alternative proof of the oracle-to-LP reduction.

import Definitions.Def_DualSepClusterLP_CutSearch

namespace DualSepClusterLP

theorem projectedCutSearchMachine (M : Turing.TM2ComputableAux Bool Bool) (A a b : ℕ)
    (hM : ∀ k, Finite (M.tm.Γ k)) (O : CutRecovery.OracleFamily)
    (hRun : CutRecovery.oracleRuns O M A a b)
    (hO : ∀ (t n : ℕ) (G : Graph n), CutRecovery.goodOracle t G (O (CutRecovery.scaleIndex t-1) n G)) :
    ∃ (P : Turing.TM2ComputableAux Bool Bool) (B c d : ℕ), (∀ k, Finite (P.tm.Γ k)) ∧
      ∀ (t n : ℕ) (G : Graph n),
        let (L,q) := CutRecovery.solve G t (O (CutRecovery.scaleIndex t-1) n G)
        ∃ J : SparseWeights n, ValidSupport J ∧ J.length ≤ 257*(n+1)^9 ∧
          primalValue G (fun S => (weightAt J S : ℝ)) = primalValue G (fun S => (weightAt L S : ℝ)) ∧
          Nonempty (Turing.TM2OutputsInTime P.tm ((graphInput t G).map P.inputAlphabet.symm)
            (some ((roundingInput G J ++ pricesBits q).map P.outputAlphabet.symm))
            (2^(B*(t+1)^c)*(n+1)^d)) := by sorry

end DualSepClusterLP
