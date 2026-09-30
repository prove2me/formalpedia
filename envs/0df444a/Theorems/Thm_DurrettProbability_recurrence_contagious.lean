-- Prove2me | Theorems.Thm_DurrettProbability_recurrence_contagious
-- name    : DurrettProbability.recurrence_contagious
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T17:24:15.288052+00:00
-- url     : https://prove2.me/theorems/8b0abf90-4a48-4b14-85b2-dedb8856a3a0
-- title:
--   Theorem 5.3.2 — recurrence is contagious
-- statement:
--   If $x$ is recurrent and $\rho_{xy}>0$ — the chain started at $x$ has some chance of reaching $y$ —
--   then $y$ is recurrent too, and moreover $\rho_{yx}=1$: from $y$ the chain returns to $x$ with
--   probability one.
--
--   The second conclusion is the sharper one and it comes first in the proof. If $\rho_{yx}$ were less
--   than one, then starting from $x$ the chain could reach $y$ and then fail ever to return, which
--   would make $\rho_{xx}<1$ and contradict the recurrence of $x$. Once $\rho_{yx}=1$ is known, $y$
--   inherits recurrence: from $y$ the chain reaches $x$ surely, from $x$ it returns to $x$ surely and
--   can reach $y$ again, and the return series at $y$ diverges with the one at $x$.
--
--   The consequence is that recurrence is a property of a communicating class, not of an individual
--   state, which is what makes the decomposition of the state space into closed irreducible recurrent
--   classes possible.
--
--   **Formalization Note** Both conclusions are asserted, since the second is what the first is proved
--   from and is the more useful of the two. No assumption is made about $\rho_{yx}$ beyond what is
--   derived.
-- source:
--   Durrett, Probability: Theory and Examples, Version 5 (11 January 2019), p. 282 (PDF p. 290), Theorem 5.3.2: 'If x is recurrent and rho_{xy} > 0 then y is recurrent and rho_{yx} = 1.' Durrett introduces it with 'The next result shows that recurrence is contagious.' sha256 aeac36cbf5e44c53d69fa60a2d29a393e2d0e8c955ee103bd845d925fd910886

import Mathlib
import Definitions.Def_DurrettProbability_MarkovChain

open Filter

namespace DurrettProbability

theorem recurrence_contagious {S : Type*} [Countable S] [DecidableEq S]
    (p : S → S → ℝ) (hp : IsTransition p) (x y : S)
    (hx : Recurrent p x) (hxy : 0 < hitProb p x y) :
    Recurrent p y ∧ hitProb p y x = 1 := by sorry

end DurrettProbability
