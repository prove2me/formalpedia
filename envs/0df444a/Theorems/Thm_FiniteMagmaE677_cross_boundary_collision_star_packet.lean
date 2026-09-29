-- Prove2me | Theorems.Thm_FiniteMagmaE677_cross_boundary_collision_star_packet
-- name    : FiniteMagmaE677.cross_boundary_collision_star_packet
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-15T03:04:52.512096+00:00
-- url     : https://prove2.me/theorems/c9579426-a17e-474f-8e9f-a14b18e0e1ee
-- title:
--   Structural packet forced by a cross-boundary collision with one element outside the left orbit
-- statement:
--   Proved supporting lemma for the one-element left-orbit-complement branch of the finite E677 → E255 problem.
--
--   Let $(\alpha,\diamond)$ be a finite magma satisfying E677: for all $p,q\in\alpha$,
--   $$p=q\diamond\bigl(p\diamond((q\diamond p)\diamond q)\bigr).$$
--   Fix $x\in\alpha$ and let $O_x=\{L_x^n(x):n\ge 0\}$ be its orbit under the left translation $L_x(z)=x\diamond z$. Assume:
--
--   1. $x$ has no right fixer, that is, no $y$ satisfies $y\diamond x=x$;
--   2. exactly one element $A$ lies outside $O_x$;
--   3. some $c\in O_x$ collides with $A$ under right translation by $x$: $c\diamond x=A\diamond x$.
--
--   Write $d=A\diamond x$, $b=A\diamond A$, $u=c\diamond d$, and $v=A\diamond u$. The lemma asserts the following structural packet.
--
--   - $d\in O_x$, $d\ne x$, $d\ne A$.
--   - $b\in O_x$, $b\ne x$, $b\ne d$, $b\ne A$.
--   - The outsider is fixed by $L_x$ and satisfies $A\diamond d=A$ and $b\diamond A=x$:
--   $$x\diamond A=A,\qquad A\diamond(A\diamond x)=A,\qquad (A\diamond A)\diamond A=x.$$
--   - The collision transports along the backward recurrence: $u\diamond c=b$.
--   - $u\in O_x$ and $u\ne d$.
--   - $v\in O_x$, $v\ne A$, $v\ne b$.
--   - If $v=d$, then $u=x$, and the two predecessor identities
--   $$x\diamond(d\diamond c)=d,\qquad d\diamond(x\diamond c)=x$$
--   hold, so $L_c$ exchanges $x$ and $d$.
--
--   The lemma isolates the points and separations that any argument about the cross-boundary collision must handle, and it splits the situation into the branch $v=d$ and the branch $v\ne d$. It does not conclude the open successor-propagation statement $(x\diamond c)\diamond x=A\diamond x$, and it does not produce a fixer. Its conclusions are sound constraints for finite-model or SAT searches inside this branch.
--
--   **Formalization Note** Orbit membership is the predicate `InLeftOrbit`, the no-fixer hypothesis is the negation of `HasFixerAt`, and uniqueness of the outsider is stated as: every element outside the orbit equals $A$. The derived points are written out as terms rather than introduced by `let` binders.
-- source:
--   Supporting lemma for the finite E677 to E255 formalization, mission 508ccd7b-8791-4bdf-883c-9a44bd760881, one-element left-orbit-complement branch feeding theorem FiniteMagmaE677.cross_boundary_collision_propagates_to_left_successor; Equational Theories Project blueprint, Chapter 13, https://teorth.github.io/equational_theories/blueprint/677-chapter.html; Bolan et al., arXiv:2512.07087v2, Section 8, Problem 8.1.

import Definitions.Def_FiniteMagmaE677

universe u

theorem FiniteMagmaE677.cross_boundary_collision_star_packet
    {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
    (x A c : α)
    (hnofix : ¬ FiniteMagmaE677.HasFixerAt op x)
    (hA_notin : ¬ FiniteMagmaE677.InLeftOrbit op x A)
    (hA_unique : ∀ a : α, ¬ FiniteMagmaE677.InLeftOrbit op x a → a = A)
    (hc : FiniteMagmaE677.InLeftOrbit op x c)
    (hcollision : op c x = op A x) :
    FiniteMagmaE677.InLeftOrbit op x (op A x) ∧
      op A x ≠ x ∧
      op A x ≠ A ∧
      FiniteMagmaE677.InLeftOrbit op x (op A A) ∧
      op A A ≠ x ∧
      op A A ≠ op A x ∧
      op A A ≠ A ∧
      op x A = A ∧
      op A (op A x) = A ∧
      op (op A A) A = x ∧
      op (op c (op A x)) c = op A A ∧
      FiniteMagmaE677.InLeftOrbit op x (op c (op A x)) ∧
      op c (op A x) ≠ op A x ∧
      FiniteMagmaE677.InLeftOrbit op x (op A (op c (op A x))) ∧
      op A (op c (op A x)) ≠ A ∧
      op A (op c (op A x)) ≠ op A A ∧
      (op A (op c (op A x)) = op A x →
        op c (op A x) = x ∧
          op x (op (op A x) c) = op A x ∧
          op (op A x) (op x c) = x) := by sorry
