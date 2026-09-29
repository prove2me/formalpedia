-- Prove2me | Theorems.Thm_FiniteMagmaE677_period_four_orbit_right_collision_gives_first_return_or_fixer
-- name    : FiniteMagmaE677.period_four_orbit_right_collision_gives_first_return_or_fixer
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-23T20:38:28.495288+00:00
-- url     : https://prove2.me/theorems/a2f428a2-ca92-4766-b996-836f3a046483
-- title:
--   D4.2 — Tagged finite first-return reduction
-- statement:
--   Let a finite magma satisfy E677. Suppose left multiplication by $x$ has the exact four-cycle
--
--   $$x\longmapsto c_1\longmapsto c_2\longmapsto c_3\longmapsto x,$$
--
--   with $x$ distinct from the other three displayed points. Suppose distinct elements $a,b$ on this orbit satisfy $a\diamond x=b\diamond x$. Then
--
--   $$\text{a tagged exact first-return packet exists}\quad\text{or}\quad\exists y,\ y\diamond x=x.$$
--
--   In the packet alternative put $q=c_2\diamond x$, $r=c_1\diamond c_2$, $s=c_3\diamond q$. The packet retains the q-collision, $c_1\diamond q=x$, $c_2\diamond q=c_1$, and all four base points and q as distinct elements. Its five possible initialized branches are:
--
--   1. R through one step: r is outside the base and q, and $L_x(q)$ is outside those six points; use seed q and depth 1.
--   2. R through two steps: r is outside the base and q, $L_x(q)=r$, and $L_x(r)$ is outside those six points; use seed q and depth 2.
--   3. S through one step: $r=c_1$, s is outside the base and q, and $L_x(q)$ is outside those six points; use seed q and depth 1.
--   4. S through two steps: $r=c_1$, s is outside the base and q, $L_x(q)=s$, and $L_x(s)$ is outside those six points; use seed q and depth 2.
--   5. Swapped S: $r=c_1$, s is outside the base and q, and $L_x(q)=s$, $L_x(s)=q$. The new seed $t=c_2\diamond s$ is outside those six points and satisfies $t\diamond c_2=c_3$; use depth 0.
--
--   For the selected seed v and depth n, the packet supplies its positive minimal return period $d>n$. All of
--
--   $$v,L_x(v),\ldots,L_x^{d-1}(v)$$
--
--   are pairwise distinct and outside the four-element base cycle, and $L_x^d(v)=v$. All branch equations and the initialized trace remain available. This gives an exact finite-cycle reduction; it does not claim that those cycles collapse or yield a fixer for x.
-- source:
--   Adam McKenna, The Missing Pair, revision 9b76827c2246f0e6288466768f15b5c6f9350d71; Piece1D4FirstReturn.lean, e677_minimalPeriodFour_orbitRightCollision_hasFixer_or_firstReturnPacket; trace ingress in Piece1D4TaggedTraceStart.lean and Piece1D4TraceInitialization.lean. https://github.com/flound1129/the-missing-pair/blob/9b76827c2246f0e6288466768f15b5c6f9350d71/lean/E677/Spine/Piece1D4FirstReturn.lean

import Definitions.Def_FiniteMagmaE677_d4_first_return

universe u

open FiniteMagmaE677.FirstReturn

theorem FiniteMagmaE677.period_four_orbit_right_collision_gives_first_return_or_fixer
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
    (hcollision : op a x = op b x)
    : Nonempty (FiniteMagmaE677.FirstReturn.D4FirstReturnPacket op x c1 c2 c3) ∨
      FiniteMagmaE677.HasFixerAt op x := by sorry
