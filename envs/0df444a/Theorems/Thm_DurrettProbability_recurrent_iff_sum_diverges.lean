-- Prove2me | Theorems.Thm_DurrettProbability_recurrent_iff_sum_diverges
-- name    : DurrettProbability.recurrent_iff_sum_diverges
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T17:23:19.780958+00:00
-- url     : https://prove2.me/theorems/ad2adbd7-bd19-4de0-ba40-449af31662b2
-- title:
--   Theorem 5.3.1 — recurrence is divergence of the return series
-- statement:
--   Let $N(y)$ be the number of visits the chain makes to $y$ at positive times, so that
--   $\mathbb{E}_yN(y)=\sum_{n\ge1}p^n(y,y)$. Then
--   $$y \text{ is recurrent}\quad\Longleftrightarrow\quad \sum_{n\ge1}p^n(y,y)=\infty .$$
--
--   This is the bridge between the two ways of looking at a chain. Recurrence is defined by a hitting
--   probability, $\rho_{yy}=1$, which is a statement about first passages; the criterion restates it as
--   divergence of a series of matrix entries, which is computable. Almost every concrete recurrence
--   verification — random walks in dimensions one, two and three among them — goes through this form.
--
--   The mechanism is the renewal identity $p^n(x,y)=\sum_{m\le n}f^m(x,y)\,p^{n-m}(y,y)$, which in
--   generating-function form reads $P(s)=1/(1-F(s))$ at $x=y$: the return series diverges exactly when
--   $F(1)=\rho_{yy}$ reaches one.
--
--   **Formalization Note** "$\sum_{n\ge1}p^n(y,y)=\infty$" is stated as failure of summability, which
--   for a series of non-negative terms is exactly divergence, and avoids introducing extended reals.
--   The visit count $N(y)$ is not itself formalized, since the chain's law on path space is not
--   constructed; the statement is about the series, which is what $\mathbb{E}_yN(y)$ equals.
-- source:
--   Durrett, Probability: Theory and Examples, Version 5 (11 January 2019), p. 282 (PDF p. 290), Theorem 5.3.1: 'y is recurrent if and only if E_y N(y) = infinity.' Here N(y) is the number of visits to y at positive times, so E_y N(y) = sum_{n >= 1} p^n(y,y). sha256 aeac36cbf5e44c53d69fa60a2d29a393e2d0e8c955ee103bd845d925fd910886

import Mathlib
import Definitions.Def_DurrettProbability_MarkovChain

open Filter

namespace DurrettProbability

theorem recurrent_iff_sum_diverges {S : Type*} [Countable S] [DecidableEq S]
    (p : S → S → ℝ) (hp : IsTransition p) (y : S) :
    Recurrent p y ↔ ¬ Summable (fun n : ℕ => stepProb p (n + 1) y y) := by sorry

end DurrettProbability
