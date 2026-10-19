-- Prove2me | Theorems.Thm_FiniteMagmaE677_e677_implies_e255_finite_of_two_left_orbit_complement_escape
-- name    : FiniteMagmaE677.e677_implies_e255_finite_of_two_left_orbit_complement_escape
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-17T05:10:39.076444+00:00
-- url     : https://prove2.me/theorems/5ee82bdf-ba18-47ce-8280-2645eda38122
-- title:
--   Sub-goal 3 for all finite E677 magmas implies E255 (product transport)
-- statement:
--   Let $\alpha$ be a finite type with an arbitrary total operation $\diamond$ satisfying E677. For $x\in\alpha$ write $L_x(z)=x\diamond z$; the left orbit of $x$ is $\{L_x^n(x):n\ge 0\}$, and a fixer of $x$ is an element $y$ with $y\diamond x=x$.
--
--   Let (H) be the following statement, which is Sub-goal 3 of this mission for every finite carrier in the universe of $\alpha$:
--
--   1. for every finite type $\beta$ with an operation $\diamond$ satisfying E677,
--   2. for every $x\in\beta$ with $x\diamond x\ne x$,
--   3. if at least two distinct elements of $\beta$ lie outside the left orbit of $x$, and right translation by $x$ sends some element of that orbit outside the orbit,
--   4. then $x$ has a fixer.
--
--   If (H) holds, then E255 holds in $\alpha$:
--
--   $$\forall x\in\alpha,\quad x=((x\diamond x)\diamond x)\diamond x.$$
--
--   Conversely, the mission goal gives (H), because E255 at $x$ supplies the fixer $(x\diamond x)\diamond x$. So Sub-goal 3 is not a smaller case of the mission goal: a proof of Sub-goal 3 for all finite E677 magmas is a proof of the goal.
--
--   **Formalization Note** (H) is a hypothesis quantified over all finite types in the universe of $\alpha$; its type is exactly the type of `FiniteMagmaE677.two_left_orbit_complement_elements_escape_gives_fixer`. Empty carriers are included.
-- source:
--   Adam McKenna, The Missing Pair (private repository), revision 4100763b, lean/E677/Transport.lean, e677_fixer_exists_of_d7_leaf and e677_implies_e255_of_d7_leaf; mission Sub-goal 3 is theorem FiniteMagmaE677.two_left_orbit_complement_elements_escape_gives_fixer.

import Definitions.Def_FiniteMagmaE677

universe u

theorem FiniteMagmaE677.e677_implies_e255_finite_of_two_left_orbit_complement_escape
    (hSG3 : ∀ {β : Type u} [Fintype β] (op : β → β → β), FiniteMagmaE677.E677 op →
      ∀ x : β, op x x ≠ x →
        (∃ a b : β, a ≠ b ∧
          ¬ FiniteMagmaE677.InLeftOrbit op x a ∧ ¬ FiniteMagmaE677.InLeftOrbit op x b) →
        (∃ a : β, FiniteMagmaE677.InLeftOrbit op x a ∧
          ¬ FiniteMagmaE677.InLeftOrbit op x (op a x)) →
        FiniteMagmaE677.HasFixerAt op x)
    {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op) :
    FiniteMagmaE677.E255 op := by sorry
