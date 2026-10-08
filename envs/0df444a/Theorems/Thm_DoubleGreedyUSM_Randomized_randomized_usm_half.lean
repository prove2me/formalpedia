-- Prove2me | Theorems.Thm_DoubleGreedyUSM_Randomized_randomized_usm_half
-- name    : DoubleGreedyUSM.Randomized.randomized_usm_half
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:10:37.891198+00:00
-- url     : https://prove2.me/theorems/37d637bf-bf40-4814-b721-1e436128748d
-- title:
--   Theorem I.2 — randomized double greedy achieves half the optimum
-- statement:
--   Let $f:2^{\mathcal N}\to\mathbb R_{\ge0}$ be a submodular set function on a finite ground set, and let $u_1,\ldots,u_n$ be any order of its elements. Run the randomized double-greedy Algorithm 2 and let $X_n$ be its output. If $OPT=\max_{S\subseteq\mathcal N} f(S)$, then
--
--   $$OPT\le 2\,\mathbb E[f(X_n)].$$
--
--   Thus the algorithm attains the paper's one-half approximation ratio in expectation, including when the optimum is zero.
--
--   **Formalization Note** The theorem concerns the specific Algorithm 2 law and every enumeration of the ground set. It encodes the approximation inequality, while the paper's linear-time and value-oracle complexity claims are outside the Lean statement. The output identity $X_n=Y_n$ is stated separately in the endpoint milestone.
-- source:
--   Buchbinder, Feldman, Naor, Schwartz, A Tight Linear Time (1/2)-Approximation for Unconstrained Submodular Maximization, FOCS 2012 version, Theorem I.2 (PDF p. 2), proof (PDF p. 5)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_DoubleGreedyUSM_Randomized_Algorithm2

namespace DoubleGreedyUSM.Randomized

/-- Theorem I.2 (PDF p. 2): Algorithm 2 has expected output at least half the optimum. -/
theorem randomized_usm_half {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (hf0 : ∀ S : Finset X, 0 ≤ f S)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x : X, x ∈ l) :
    NonmonotoneSubmod.Shared.OPT f ≤
      2 * expect (state f l l.length) (fun s => f s.1) := by sorry

end DoubleGreedyUSM.Randomized
