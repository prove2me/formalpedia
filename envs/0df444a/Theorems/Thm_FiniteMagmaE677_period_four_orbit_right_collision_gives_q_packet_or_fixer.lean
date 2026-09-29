-- Prove2me | Theorems.Thm_FiniteMagmaE677_period_four_orbit_right_collision_gives_q_packet_or_fixer
-- name    : FiniteMagmaE677.period_four_orbit_right_collision_gives_q_packet_or_fixer
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-15T04:42:20.616148+00:00
-- url     : https://prove2.me/theorems/4fe27e0f-1457-4798-9a10-3e49016b9728
-- title:
--   A right-translation collision on a period-four left orbit gives the q-packet or a fixer
-- statement:
--   Let $(\alpha,\diamond)$ be a finite magma satisfying E677: for all $p,q\in\alpha$,
--   $$p=q\diamond\bigl(p\diamond((q\diamond p)\diamond q)\bigr).$$
--   Fix $x\in\alpha$ and suppose the left orbit of $x$ under $L_x(z)=x\diamond z$ has minimal period four. Concretely, name the orbit points
--   $$c_1=x\diamond x,\qquad c_2=x\diamond c_1,\qquad c_3=x\diamond c_2,$$
--   and assume $x\diamond c_3=x$ together with $x\ne c_1$, $x\ne c_2$, $x\ne c_3$. Suppose two distinct points $a\ne b$ of the orbit collide under right translation by $x$:
--   $$a\diamond x=b\diamond x.$$
--   Write $q=c_2\diamond x$, $r=c_1\diamond c_2$, and $s=c_3\diamond q$. Then at least one of the following holds.
--
--   1. $x$ has a right fixer: some $y$ satisfies $y\diamond x=x$.
--   2. The collision normalizes to the distinguished $q$-packet
--   $$c_2\diamond x=c_3\diamond x,\qquad c_1\diamond q=x,\qquad c_2\diamond q=c_1,$$
--   the element $q$ lies outside $\{x,c_1,c_2,c_3\}$, and a second fresh element is identified by one of two tagged branches:
--      - the $r$-branch: $r\notin\{x,c_1,c_2,c_3,q\}$; or
--      - the $s$-branch: $r=c_1$ and $s\notin\{x,c_1,c_2,c_3,q\}$.
--
--   In the period-four case, this reduces an arbitrary right-translation collision on the orbit to a single normal form, with at least six distinct named elements, unless a fixer already exists. It does not decide whether the normal form can occur, so it does not prove the orbit right-collision theorem for period four.
--
--   **Formalization Note** Minimal period four is stated as closure $x\diamond c_3=x$ together with the three inequalities $x\ne c_i$, which exclude periods one, two, and three. Orbit membership is the predicate `InLeftOrbit`, and the fixer alternative is `HasFixerAt`. The terms $q$, $r$, $s$ are written out in full.
-- source:
--   Period-four case of the orbit right-collision theorem FiniteMagmaE677.orbit_right_collision_or_fixer, mission 508ccd7b-8791-4bdf-883c-9a44bd760881; Equational Theories Project blueprint, Chapter 13, https://teorth.github.io/equational_theories/blueprint/677-chapter.html; Bolan et al., arXiv:2512.07087v2, Section 8, Problem 8.1.

import Definitions.Def_FiniteMagmaE677

universe u

theorem FiniteMagmaE677.period_four_orbit_right_collision_gives_q_packet_or_fixer
    {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
    (x c1 c2 c3 : α)
    (hc1 : op x x = c1)
    (hc2 : op x c1 = c2)
    (hc3 : op x c2 = c3)
    (hcloses : op x c3 = x)
    (hx_ne_c1 : x ≠ c1)
    (hx_ne_c2 : x ≠ c2)
    (hx_ne_c3 : x ≠ c3)
    (a b : α)
    (ha : FiniteMagmaE677.InLeftOrbit op x a)
    (hb : FiniteMagmaE677.InLeftOrbit op x b)
    (hab : a ≠ b)
    (hcollision : op a x = op b x) :
    (op c2 x = op c3 x ∧
      op c1 (op c2 x) = x ∧
      op c2 (op c2 x) = c1 ∧
      op c2 x ≠ x ∧
      op c2 x ≠ c1 ∧
      op c2 x ≠ c2 ∧
      op c2 x ≠ c3 ∧
      ((op c1 c2 ≠ x ∧
          op c1 c2 ≠ c1 ∧
          op c1 c2 ≠ c2 ∧
          op c1 c2 ≠ c3 ∧
          op c1 c2 ≠ op c2 x) ∨
        (op c1 c2 = c1 ∧
          op c3 (op c2 x) ≠ x ∧
          op c3 (op c2 x) ≠ c1 ∧
          op c3 (op c2 x) ≠ c2 ∧
          op c3 (op c2 x) ≠ c3 ∧
          op c3 (op c2 x) ≠ op c2 x))) ∨
      FiniteMagmaE677.HasFixerAt op x := by sorry
