-- Prove2me | Theorems.Thm_FiniteMagmaE677_period_four_fixed_seed_cycle_gives_fixer
-- name    : FiniteMagmaE677.period_four_fixed_seed_cycle_gives_fixer
-- status  : Open
-- author  : @mysticflounder
-- created : 2026-09-23T20:38:39.171854+00:00
-- url     : https://prove2.me/theorems/98f7dc30-3fa6-4160-89d8-62bd30c5e338
-- title:
--   D4.3b — Transfer from the fixed outsider seed
-- statement:
--   **CONJECTURED — open branch closeout.** Let a finite set carry an arbitrary binary operation $\diamond$ satisfying E677:
--
--   $$z=y\diamond\bigl(z\diamond((y\diamond z)\diamond y)\bigr)\quad\text{for all }z,y.$$
--
--   Write $L_x(z)=x\diamond z$. The distinguished packet records four pairwise distinct points with
--
--   $$L_x(x)=c_1,\quad L_x(c_1)=c_2,\quad L_x(c_2)=c_3,\quad L_x(c_3)=x.$$
--
--   Set $q=c_2\diamond x$, $r=c_1\diamond c_2$, and $s=c_3\diamond q$. The packet also records that $q$ is outside the four displayed points and
--
--   $$q=c_3\diamond x,\qquad c_1\diamond q=x,\qquad c_2\diamond q=c_1.$$
--
--   A first-return packet for a seed $v$ through depth $n$ supplies its positive minimal return period $d>n$. The points $v,L_x(v),\ldots,L_x^{d-1}(v)$ are pairwise distinct and outside the four displayed points, and $L_x^d(v)=v$. The initialized prefix and all tagged branch equations are retained as hypotheses.
--
--   Assume the R branch, with $r$ outside $\{x,c_1,c_2,c_3,q\}$, $L_x(q)=r$, and $L_x(r)$ outside $\{x,c_1,c_2,c_3,q,r\}$. Retain the tagged R start and the first-return packet of $q$ through depth $2$. Also assume the source-derived contact fact that $q$ has a fixer: some $w$ satisfies $w\diamond q=q$.
--
--   The target is a fixer for the original base point:
--
--   $$\exists y,\quad y\diamond x=x.$$
--
--   This is one retained branch of the period-four orbit-collision problem. The cycle data and local contact facts are established inputs; the displayed fixer conclusion is still open. No bound on the size of the finite carrier is imposed.
-- source:
--   Adam McKenna, The Missing Pair, revision 9b76827c2246f0e6288466768f15b5c6f9350d71; lean/E677/Spine/Piece1D4CycleContact.lean, E677D4QCycleContactBranch and e677_d4_q_cycleContactPacket_of_firstReturnPacket; docs/current/e677-closure-plan-2026-08-04.md, D4 first-return collapse frontier. https://github.com/flound1129/the-missing-pair/blob/9b76827c2246f0e6288466768f15b5c6f9350d71/lean/E677/Spine/Piece1D4CycleContact.lean

import Definitions.Def_FiniteMagmaE677_d4_first_return

universe u

open FiniteMagmaE677.FirstReturn

theorem FiniteMagmaE677.period_four_fixed_seed_cycle_gives_fixer
    {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
    (x c1 c2 c3 : α)
    (packet : D4Distinguished op x c1 c2 c3)
    (start : RTaggedStart op x c1 c2 c3)
    (q_to_r : op x (op c2 x) = op c1 c2)
    (fresh : FreshOutsideSix x c1 c2 c3 (op c2 x) (op c1 c2) (op x (op c1 c2)))
    (initial_trace : D4Trace op x c1 c2 c3 (op c2 x) 2)
    (first_return : D4FirstReturn op x c1 c2 c3 (op c2 x) 2)
    (seed_fixer : FiniteMagmaE677.HasFixerAt op (op c2 x))
    : FiniteMagmaE677.HasFixerAt op x := by sorry
