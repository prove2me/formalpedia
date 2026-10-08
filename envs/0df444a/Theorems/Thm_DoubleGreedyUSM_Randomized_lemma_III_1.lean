-- Prove2me | Theorems.Thm_DoubleGreedyUSM_Randomized_lemma_III_1
-- name    : DoubleGreedyUSM.Randomized.lemma_III_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:10:20.393977+00:00
-- url     : https://prove2.me/theorems/1d081209-7556-4e2e-8d96-817ee5f78a1e
-- title:
--   Lemma III.1 — expected comparison loss versus expected algorithm gain
-- statement:
--   Let $f:2^{\mathcal N}\to\mathbb R_{\ge0}$ be submodular, let $OPT$ be an optimal set, and run Algorithm 2 in any order. Write $OPT_i=(OPT\cup X_i)\cap Y_i$. For each $1\le i\le n$, expectations over the algorithm's random choices satisfy
--
--   $$\mathbb E[f(OPT_{i-1})-f(OPT_i)]\le\frac12\,\mathbb E[f(X_i)-f(X_{i-1})+f(Y_i)-f(Y_{i-1})].$$
--
--   This is the local estimate whose sum yields Theorem I.2.
--
--   **Formalization Note** Each expectation is an exact finite sum over the corresponding time's state law. Linearity writes the expected difference as a difference of expectations under those two marginal laws; this equals the expectation of the difference along a run.
-- source:
--   Buchbinder, Feldman, Naor, Schwartz, A Tight Linear Time (1/2)-Approximation for Unconstrained Submodular Maximization, FOCS 2012 version, Lemma III.1, inequality (1) (PDF p. 5)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_DoubleGreedyUSM_Randomized_Algorithm2

namespace DoubleGreedyUSM.Randomized

/-- Lemma III.1, inequality (1) (PDF p. 5), with expectations under the two marginal laws. -/
theorem lemma_III_1 {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (hf0 : ∀ S : Finset X, 0 ≤ f S)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x : X, x ∈ l)
    (O : Finset X) (hO : ∀ S : Finset X, f S ≤ f O) :
    ∀ i (hi : 1 ≤ i) (hin : i ≤ l.length),
      expect (state f l (i - 1)) (fun s => f (DoubleGreedyUSM.Deterministic.optI O s)) -
        expect (state f l i) (fun s => f (DoubleGreedyUSM.Deterministic.optI O s)) ≤
      (1 / 2 : ℝ) *
        (expect (state f l i) (fun s => f s.1 + f s.2) -
          expect (state f l (i - 1)) (fun s => f s.1 + f s.2)) := by sorry

end DoubleGreedyUSM.Randomized
