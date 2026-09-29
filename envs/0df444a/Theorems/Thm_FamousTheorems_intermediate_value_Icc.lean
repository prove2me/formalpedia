-- Prove2me | Theorems.Thm_FamousTheorems_intermediate_value_Icc
-- name    : FamousTheorems.intermediate_value_Icc
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:10:36.919213+00:00
-- url     : https://prove2.me/theorems/62a5d489-9ea6-46f4-a357-42b0074b0cfa
-- title:
--   The intermediate value theorem
-- statement:
--   **A continuous function attains every intermediate value.**
--
--   For continuous $f$ on $[a,b]$ with $a \le b$, every value between $f(a)$ and $f(b)$ is attained:
--   $$[f(a), f(b)] \subseteq f\bigl([a,b]\bigr).$$
--
--   The theorem is really about **connectedness**: the continuous image of a connected set is
--   connected, and the connected subsets of $\mathbb{R}$ are precisely the intervals. It therefore
--   fails over $\mathbb{Q}$ — $x^2 - 2$ changes sign on $[0,2] \cap \mathbb{Q}$ without vanishing
--   there — so it encodes completeness of $\mathbb{R}$.
--
--   Bolzano gave the first rigorous proof in 1817, as part of the programme of founding analysis on
--   arithmetic rather than geometric intuition.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem intermediate_value_Icc : ∀ {a b : ℝ}, a ≤ b → ∀ {f : ℝ → ℝ},
    ContinuousOn f (Set.Icc a b) → Set.Icc (f a) (f b) ⊆ f '' Set.Icc a b := by sorry

end FamousTheorems
