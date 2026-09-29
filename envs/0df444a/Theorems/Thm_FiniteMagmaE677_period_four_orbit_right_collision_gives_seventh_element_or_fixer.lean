-- Prove2me | Theorems.Thm_FiniteMagmaE677_period_four_orbit_right_collision_gives_seventh_element_or_fixer
-- name    : FiniteMagmaE677.period_four_orbit_right_collision_gives_seventh_element_or_fixer
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-23T20:29:48.78019+00:00
-- url     : https://prove2.me/theorems/ecba396a-0d63-44e2-bce1-19a639f342bd
-- title:
--   D4.1 — Seven-element growth or a fixer
-- statement:
--   Let a finite magma satisfy E677,
--
--   $$z=y\diamond\bigl(z\diamond((y\diamond z)\diamond y)\bigr).$$
--
--   Suppose the left orbit of $x$ has exact period four, displayed as
--
--   $$x\longmapsto c_1\longmapsto c_2\longmapsto c_3\longmapsto x,$$
--
--   under $L_x(z)=x\diamond z$, with $x$ distinct from $c_1,c_2,c_3$. Suppose distinct orbit elements $a,b$ satisfy $a\diamond x=b\diamond x$. Then either $x$ has a fixer, or the following tagged seven-element growth packet exists.
--
--   Put $q=c_2\diamond x$, $r=c_1\diamond c_2$, and $s=c_3\diamond q$. The packet retains
--
--   $$q=c_3\diamond x,\qquad c_1\diamond q=x,\qquad c_2\diamond q=c_1,$$
--
--   and $q\notin\{x,c_1,c_2,c_3\}$. It has one of two branches:
--
--   1. $r\notin\{x,c_1,c_2,c_3,q\}$, and at least one of $L_x(q),L_x(r)$ is outside $\{x,c_1,c_2,c_3,q,r\}$.
--   2. $r=c_1$, $s\notin\{x,c_1,c_2,c_3,q\}$, and at least one of $L_x(q),L_x(s),c_2\diamond s$ is outside $\{x,c_1,c_2,c_3,q,s\}$.
--
--   Thus the conclusion is
--
--   $$\text{a tagged seven-element packet}\quad\text{or}\quad\exists y,\ y\diamond x=x.$$
--
--   The growth alternative provides seven distinct elements with explicit source terms. It is one finite growth step under an exact period-four collision; it neither iterates the construction nor proves the general finite E677 implication.
-- source:
--   Adam McKenna, The Missing Pair, revision 9b76827c2246f0e6288466768f15b5c6f9350d71; Piece1D4SeventhElementGrowth.lean, e677_minimalPeriodFour_orbitRightCollision_hasFixer_or_seventhElementGrowth; R/S branch algebra in Piece1D4RBranchGrowth.lean and Piece1D4SBranchGrowth.lean. https://github.com/flound1129/the-missing-pair/blob/9b76827c2246f0e6288466768f15b5c6f9350d71/lean/E677/Spine/Piece1D4SeventhElementGrowth.lean

import Definitions.Def_FiniteMagmaE677_seventh_element_growth

universe u

theorem FiniteMagmaE677.period_four_orbit_right_collision_gives_seventh_element_or_fixer
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
    FiniteMagmaE677.SeventhElementGrowth op x c1 c2 c3 ∨
      FiniteMagmaE677.HasFixerAt op x := by sorry
