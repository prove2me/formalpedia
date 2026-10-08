-- Prove2me | Theorems.Thm_DialARideBC_Valid_subtour_bound
-- name    : DialARideBC.Valid.subtour_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:43.483143+00:00
-- url     : https://prove2.me/theorems/5f389058-1c48-410c-b512-4c67ca113e2b
-- title:
--   §4.2 (p. 576) and proof of Proposition 5 (p. 578) — x(S) ≤ |S| − 1 for every nonempty S ⊆ P ∪ D
-- statement:
--   Consider a DARP instance with $n$ users and a feasible solution with total arc flows $x_{ij}$. For every nonempty node set $S \subseteq P \cup D$, the simple subtour elimination constraint holds:
--   $$x(S) = \sum_{i,j\in S} x_{ij} \le |S| - 1.$$
--
--   This is the starting point of all liftings in §4.2 and the first observation of the proof of Proposition 5, where it is applied to the handle $H$ and to every tooth $T_h$.
--
--   **Formalization Note.** The set $S$ is required to be nonempty: for $S = \emptyset$ the inequality reads $0 \le -1$. In the proof of Proposition 5 the sets $H$ and $T_h$ contain $i_h$, so they are nonempty.
-- source:
--   Cordeau, A Branch-and-Cut Algorithm for the Dial-a-Ride Problem, Oper. Res. 54(3) (2006), p. 576, §4.2 (simple subtour elimination constraint) and p. 578, proof of Proposition 5, first sentence

import Mathlib
import Definitions.Def_DialARideBC_Valid_Model

namespace DialARideBC.Valid

theorem subtour_bound {n : ℕ} {K : Type} [Fintype K] (I : Instance n K) (s : Solution I)
    (S : Finset ℕ) (hS : S ⊆ PD n) (hne : S.Nonempty) :
    xset s.x S ≤ (S.card : ℝ) - 1 := by sorry

end DialARideBC.Valid
