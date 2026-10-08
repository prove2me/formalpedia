-- Prove2me | Theorems.Thm_DoubleGreedyUSM_Randomized_telescoped_bound
-- name    : DoubleGreedyUSM.Randomized.telescoped_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:10:38.601218+00:00
-- url     : https://prove2.me/theorems/7d60181e-b0a2-4119-8264-521366ac2b72
-- title:
--   Proof of Theorem I.2 — telescoped expected loss bound
-- statement:
--   Let $f:2^{\mathcal N}\to\mathbb R_{\ge0}$ be submodular, let $OPT$ be an optimal set, and run Algorithm 2 through every element of the ground set. Its initial sets are $X_0=\varnothing$ and $Y_0=\mathcal N$. The telescoped estimate has both parts
--
--   $$f(OPT)-\mathbb E[f(OPT_n)]\le\frac12\Bigl(\mathbb E[f(X_n)+f(Y_n)]-f(\varnothing)-f(\mathcal N)\Bigr)\le\frac12\mathbb E[f(X_n)+f(Y_n)].$$
--
--   The first bound retains the endpoint values that are used in the paper's two-player welfare corollary; the second uses their nonnegativity.
--
--   **Formalization Note** The expectation is an exact finite sum over final states. The two inequalities are separate conjuncts, and $OPT_n=(OPT\cup X_n)\cap Y_n$.
-- source:
--   Buchbinder, Feldman, Naor, Schwartz, A Tight Linear Time (1/2)-Approximation for Unconstrained Submodular Maximization, FOCS 2012 version, proof of Theorem I.2, second display (PDF p. 5)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_DoubleGreedyUSM_Randomized_Algorithm2

namespace DoubleGreedyUSM.Randomized

/-- The second display in the proof of Theorem I.2 (PDF p. 5), including its last inequality. -/
theorem telescoped_bound {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (hf0 : ∀ S : Finset X, 0 ≤ f S)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x : X, x ∈ l)
    (O : Finset X) (hO : ∀ S : Finset X, f S ≤ f O) :
    let μ := state f l l.length
    f O - expect μ (fun s => f (DoubleGreedyUSM.Deterministic.optI O s)) ≤
      (1 / 2 : ℝ) * (expect μ (fun s => f s.1 + f s.2) - (f ∅ + f Finset.univ)) ∧
    (1 / 2 : ℝ) * (expect μ (fun s => f s.1 + f s.2) - (f ∅ + f Finset.univ)) ≤
      (1 / 2 : ℝ) * expect μ (fun s => f s.1 + f s.2) := by sorry

end DoubleGreedyUSM.Randomized
