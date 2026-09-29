-- Prove2me | Theorems.Thm_FiniteMagmaE677_left_orbit_positive_period
-- name    : FiniteMagmaE677.left_orbit_positive_period
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-15T04:33:55.630466+00:00
-- url     : https://prove2.me/theorems/655d4dbc-0783-46cf-bc9e-bc7d22bd3ffa
-- title:
--   Left orbits in a finite E677 magma have a positive period
-- statement:
--   Let $(\alpha,\diamond)$ be a finite magma satisfying E677: for all $p,q\in\alpha$,
--   $$p=q\diamond\bigl(p\diamond((q\diamond p)\diamond q)\bigr).$$
--   For $x\in\alpha$ write $L_x(z)=x\diamond z$ for left translation by $x$. Then the orbit of $x$ under $L_x$ returns to $x$ after a positive number of steps: there is a natural number $d$ with
--   $$d>0\qquad\text{and}\qquad L_x^{\,d}(x)=x.$$
--
--   Consequently the left orbit $O_x=\{L_x^{\,n}(x):n\ge 0\}$ is a finite cycle through $x$, and every orbit point has an orbit predecessor. This is the period-existence input for orbit arguments on the mission; it is independent of any fixer or collision hypothesis.
--
--   **Formalization Note** The iterate $L_x^{\,d}(x)$ is written `(op x)^[d] x`, matching the orbit predicate `InLeftOrbit` of the mission's definition bundle. The statement asserts existence of some positive return time, not that $d$ is minimal.
-- source:
--   Supporting lemma for the finite E677 to E255 formalization, mission 508ccd7b-8791-4bdf-883c-9a44bd760881; Equational Theories Project blueprint, Chapter 13, https://teorth.github.io/equational_theories/blueprint/677-chapter.html; Bolan et al., arXiv:2512.07087v2, Section 8, Problem 8.1.

import Definitions.Def_FiniteMagmaE677

universe u

theorem FiniteMagmaE677.left_orbit_positive_period
    {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
    (x : α) :
    ∃ d : ℕ, 0 < d ∧ (op x)^[d] x = x := by sorry
