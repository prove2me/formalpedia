-- Prove2me | Theorems.Thm_DurrettProbability_stationary_eq_inv_mean_return
-- name    : DurrettProbability.stationary_eq_inv_mean_return
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T17:25:14.94329+00:00
-- url     : https://prove2.me/theorems/a635c325-5fa9-48e1-b7aa-e2263364e8fd
-- title:
--   Theorem 5.5.11 — the stationary probability is the reciprocal mean return time
-- statement:
--   Let $p$ be irreducible with stationary distribution $\pi$. Then for every state $x$ the mean
--   return time $\mathbb{E}_xT_x=\sum_{n\ge1}n\,f^n(x,x)$ is finite, and
--   $$\pi(x)\cdot\mathbb{E}_xT_x=1,\qquad\text{that is}\qquad \pi(x)=\frac{1}{\mathbb{E}_xT_x}.$$
--
--   This gives the stationary probability a second meaning, and a purely local one. As a fixed point of
--   the transition matrix, $\pi(x)$ is a global object computed from the whole chain; as a reciprocal
--   mean return time it is determined by the excursions from $x$ alone. Durrett's own remark — that
--   the identity "seems incredible" — is a fair reaction, and the reason it holds is that the chain
--   spends, on average, one visit per excursion, so the long-run fraction of time at $x$ is one over
--   the mean excursion length.
--
--   The identity is the engine of renewal-reward arguments throughout applied probability: it converts
--   a stationary probability, which is often hard to compute, into an expected return time, which is
--   often easy, and conversely.
--
--   **Formalization Note** Finiteness of the mean return time is asserted explicitly, as summability of
--   $n\,f^n(x,x)$, rather than left to a division convention: the mean return time is an unconditional
--   sum, which would silently be zero for a divergent series, and $1/0$ would then read as the correct
--   value for the wrong reason. The identity itself is stated as a product equal to one for the same
--   reason. Irreducibility and the existence of a stationary distribution together force positive
--   recurrence, which is what makes both halves true.
-- source:
--   Durrett, Probability: Theory and Examples, Version 5 (11 January 2019), p. 306 (PDF p. 314), Theorem 5.5.11: 'If p is irreducible and has stationary distribution pi, then pi(x) = 1/E_x T_x.' Remark: 'we note that the proof will make pi(x) = 1/E_x T_x obvious, but it seems incredible.' sha256 aeac36cbf5e44c53d69fa60a2d29a393e2d0e8c955ee103bd845d925fd910886

import Mathlib
import Definitions.Def_DurrettProbability_MarkovChain

open Filter

namespace DurrettProbability

theorem stationary_eq_inv_mean_return {S : Type*} [Countable S] [DecidableEq S]
    (p : S → S → ℝ) (hp : IsTransition p) (hirr : Irreducible p)
    (π : S → ℝ) (hπ : StationaryDist p π) (x : S) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * firstPassage p (n + 1) x x)
      ∧ π x * meanReturnTime p x = 1 := by sorry

end DurrettProbability
