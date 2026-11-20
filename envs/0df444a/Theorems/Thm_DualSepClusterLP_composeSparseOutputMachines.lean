-- Prove2me | Theorems.Thm_DualSepClusterLP_composeSparseOutputMachines
-- name    : DualSepClusterLP.composeSparseOutputMachines
-- status  : Proved
-- author  : @hypercube
-- created : 2026-11-19T07:24:59.978863+00:00
-- url     : https://prove2.me/theorems/7b8296ef-3803-4cef-a8d4-6e3f84652753
-- title:
--   Polynomial-time composition through a self-delimiting cluster-LP input
-- statement:
--   Fix two deterministic bit-input/bit-output machines with finite work alphabets, together with a polynomial time bound for the second machine. A single finite-alphabet machine can perform the following operation with polynomial overhead. On a graph with accuracy index $t$, it runs the first machine at index $2t+1$. If that machine produces a valid encoded rounding input followed by any suffix, and the second machine on the rounding input returns an output within its polynomial bound, the combined machine returns the same output. Its time is polynomial in the first machine’s step bound, $t+1$ and $(n+1)^2$, with constants uniform over the graph, sparse input, suffix and output. This statement concerns deterministic machine composition and decoding of the explicit sparse format. It assumes no approximation guarantee from either component.
-- source:
--   Auxiliary machine-composition lemma for the bit-level formalization of Corollary 1.4, García-Soriano and Schohn, Approximate Dual Separation for the Cluster LP, STOC 2027 submission 79, printed page 3. https://arxiv.org/abs/2607.27829v3

import Definitions.Def_DualSepClusterLP_SparseInput

namespace DualSepClusterLP

/-- Composition for a self-delimiting sparse prefix. Run the first machine
with twice the inverse accuracy, retain the rounding input at the front of
its output, then run the second machine on that prefix. The overhead is a
fixed polynomial in the first clock and the original input size. -/
theorem composeSparseOutputMachines
    (first second : Turing.TM2ComputableAux Bool Bool)
    (hfirst : ∀ k, Finite (first.tm.Γ k))
    (hsecond : ∀ k, Finite (second.tm.Γ k)) (A₂ b₂ : ℕ) :
    ∃ (combined : Turing.TM2ComputableAux Bool Bool) (c d : ℕ),
      (∀ k, Finite (combined.tm.Γ k)) ∧
      ∀ (t n : ℕ) (G : Graph n) (L : SparseWeights n)
        (suffix output : List Bool) (s : ℕ),
      Nonempty (Turing.TM2OutputsInTime first.tm
        ((graphInput (2*t+1) G).map first.inputAlphabet.symm)
        (some ((roundingInput G L ++ suffix).map first.outputAlphabet.symm)) s) →
      Nonempty (Turing.TM2OutputsInTime second.tm
        ((roundingInput G L).map second.inputAlphabet.symm)
        (some (output.map second.outputAlphabet.symm))
        (A₂ * ((roundingInput G L).length + 1)^b₂)) →
      Nonempty (Turing.TM2OutputsInTime combined.tm
        ((graphInput t G).map combined.inputAlphabet.symm)
        (some (output.map combined.outputAlphabet.symm))
        (c * (s + (t+1) + (n+1)^2 + 1)^d)) := by sorry

end DualSepClusterLP
