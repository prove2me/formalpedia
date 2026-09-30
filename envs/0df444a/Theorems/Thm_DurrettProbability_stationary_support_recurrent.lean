-- Prove2me | Theorems.Thm_DurrettProbability_stationary_support_recurrent
-- name    : DurrettProbability.stationary_support_recurrent
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T17:24:41.922278+00:00
-- url     : https://prove2.me/theorems/ac22e1a1-2c8d-4c54-97a2-25fe0bda9e7c
-- title:
--   Theorem 5.5.10 — the support of a stationary distribution is recurrent
-- statement:
--   If $p$ has a stationary distribution $\pi$, then every state $y$ with $\pi(y)>0$ is recurrent.
--
--   The contrast Durrett draws just before this result is the point of it. Stationary *measures* exist
--   for transient chains — counting measure is stationary for simple random walk on $\mathbb{Z}^d$ in
--   every dimension, including the transient ones $d\ge3$. What rules out transience is not
--   stationarity but **normalizability**: a stationary measure with finite total mass cannot be
--   supported on transient states.
--
--   The proof is a computation with the renewal identity. Stationarity gives
--   $\pi(y)=\sum_x\pi(x)p^n(x,y)$ for every $n$, so summing over $n$ and using that $\sum_n p^n(x,y)$
--   is finite at a transient $y$ forces $\pi(y)$ to be zero.
--
--   **Formalization Note** The hypothesis is a stationary *distribution*, a probability vector, not a
--   stationary measure; that is where the finiteness that drives the argument comes from. Only
--   $\pi(y)>0$ is assumed at the state in question — nothing about the rest of the support.
-- source:
--   Durrett, Probability: Theory and Examples, Version 5 (11 January 2019), p. 305 (PDF p. 313), Theorem 5.5.10: 'If there is a stationary distribution then all states y that have pi(y) > 0 are recurrent.' Durrett precedes it with the remark that stationary measures can exist for transient chains, e.g., random walks in d >= 3. sha256 aeac36cbf5e44c53d69fa60a2d29a393e2d0e8c955ee103bd845d925fd910886

import Mathlib
import Definitions.Def_DurrettProbability_MarkovChain

open Filter

namespace DurrettProbability

theorem stationary_support_recurrent {S : Type*} [Countable S] [DecidableEq S]
    (p : S → S → ℝ) (hp : IsTransition p) (π : S → ℝ) (hπ : StationaryDist p π)
    (y : S) (hy : 0 < π y) : Recurrent p y := by sorry

end DurrettProbability
