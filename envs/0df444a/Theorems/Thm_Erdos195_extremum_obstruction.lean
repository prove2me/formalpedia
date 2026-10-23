-- Prove2me | Theorems.Thm_Erdos195_extremum_obstruction
-- name    : Erdos195.extremum_obstruction
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-22T13:51:36.533417+00:00
-- url     : https://prove2.me/theorems/3cb1e285-f803-4e15-b388-338c28ac0c62
-- title:
--   Extremum obstruction: a least element traps safe words
-- statement:
--   Let $R$ be a relation on $\mathbb{Z}$ satisfying $(\ast)$, with a least element $z$ ($z\mathrel{R}y$ for all $y\neq z$). Let $P$ be a safe list containing $z$. Then no element $M$ appearing after $z$ in $P$ can be the maximum or the minimum of $P$:
--
--   $$z\in P,\ \mathrm{Safe}_R(P),\ \mathrm{pos}_P(z)<\mathrm{pos}_P(M),\ M=\max P \text{ or } M=\min P \implies \bot.$$
--
--   This is the obstruction to running Ho's method on $\mathbb{Z}$ with a completion order that has a least element.
--
--   **Formalization Note** `compLt R P x y` holds when both lie in `P` with `x` at a smaller index, or `x ∈ P` and `y ∉ P`, or neither lies in `P` and `R x y`. `Safe R P` says there are no `a` and `r ≠ 0` with `compLt R P a (a+r)`, `compLt R P (a+r) (a+2r)` and `compLt R P (a+2r) (a+3r)`.
--
--   `P.idxOf` is the index of the first occurrence in the list.
-- source:
--   New to this mission (obstruction to transferring B. S. Ho, arXiv:2609.12780, Lemma 2 to ℤ)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem extremum_obstruction (R : ℤ → ℤ → Prop) (hB : Star R) (z : ℤ)
    (hz : ∀ y, y ≠ z → R z y) (P : List ℤ) (hS : Safe R P) (hzP : z ∈ P) (M : ℤ)
    (hMP : M ∈ P) (hzM : P.idxOf z < P.idxOf M)
    (hext : (∀ x ∈ P, x ≤ M) ∨ (∀ x ∈ P, M ≤ x)) : False := by sorry

end Erdos195
