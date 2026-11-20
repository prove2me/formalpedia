-- Prove2me | Theorems.Thm_DualSepClusterLP_deterministicApproximation
-- name    : DualSepClusterLP.deterministicApproximation
-- status  : Proved
-- author  : @hypercube
-- created : 2026-11-18T17:43:31.214101+00:00
-- url     : https://prove2.me/theorems/9c42c91f-2460-4542-bd14-329daf86b437
-- title:
--   Corollary 1.4 — a deterministic $(1.3865+\varepsilon)$-approximation
-- statement:
--   A uniform deterministic algorithm returns a clustering within $1.3865+\varepsilon$ of the optimum on every complete unweighted signed graph, in $2^{\mathrm{poly}(1/\varepsilon)}\mathrm{poly}(n)$ time. The integer accuracy index requests $\varepsilon=1/(t+1)$; this covers all positive real tolerances by rounding inverse accuracy up.
-- source:
--   David García-Soriano and Antoine Schohn, Approximate Dual Separation for the Cluster LP, STOC 2027 paper #79, §1, Corollary 1.4, printed p. 3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/79.pdf

import Mathlib
import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_DualSepClusterLP_Setting

namespace DualSepClusterLP

/-- Corollary 1.4 at additive accuracy 1/(t+1). -/
theorem deterministicApproximation :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (A a b : ℕ),
      (∀ k, Finite (M.tm.Γ k)) ∧
      ∀ (t n : ℕ) (G : Graph n), ∃ C : Clustering n,
        Nonempty (Turing.TM2OutputsInTime M.tm
          ((graphInput t G).map M.inputAlphabet.symm)
          (some ((partitionOutput C).map M.outputAlphabet.symm))
          (2 ^ (A * (t+1)^a) * (n+1)^b)) ∧
        ∀ D : Clustering n,
          2000 * (t+1) * disagreements G C ≤
            (2773 * (t+1) + 2000) * disagreements G D := by sorry

end DualSepClusterLP
