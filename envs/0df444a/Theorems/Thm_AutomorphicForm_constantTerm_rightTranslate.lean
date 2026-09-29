-- Prove2me | Theorems.Thm_AutomorphicForm_constantTerm_rightTranslate
-- name    : AutomorphicForm.constantTerm_rightTranslate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/46a22850-e8df-56ca-aa2b-03e5032758d3
-- title:
--   The constant term intertwines right translation
-- statement:
--   Let $Q$ be a measurable space, $G$ a group, $\mu$ a measure on $Q$, $u : Q \to G$ an arbitrary map, $f : G \to \mathbb{C}$ an arbitrary function, and $g, h \in G$. Here the constant term [`AutomorphicForm.constantTerm`](def/AutomorphicForm_ConstantTerm.html#L47) of a function $f$ along $u$ at a point $g$ is by definition the Bochner integral $\int_Q f(u(q)\,g)\,d\mu(q)$, the integrand being the function $q \mapsto f(u(q)\,g)$ given by [`AutomorphicForm.constantTermIntegrand`](def/AutomorphicForm_ConstantTerm.html#L44). The assertion is that the constant term along $u$ of the right translate $x \mapsto f(xh)$, evaluated at $g$, equals the constant term along $u$ of $f$ itself, evaluated at $gh$: $$\int_Q f(u(q)\,g\,h)\,d\mu(q) = \int_Q f(u(q)\,(gh))\,d\mu(q).$$ No measurability or integrability hypothesis on $f$, $u$ or the integrand is imposed, and no structure on $G$ beyond its group law is used; the identity holds for the integral as defined, both sides being the integral of the very same function of $q$.
--
--   This is the compatibility of the constant-term (period) operator with the right regular representation of $G$: translating a function on the right by $h$ and then taking constant terms is the same as taking constant terms and translating the resulting function on $G$ by $h$. It is used by [`AutomorphicForm.IsCuspidalFn.rightTranslate`](thm.html#AutomorphicForm.IsCuspidalFn.rightTranslate), i.e. to show that the vanishing of constant terms is preserved under right translation, and hence that the cuspidal subspace is stable under the right regular action and under operators built from it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_constantTerm_rightTranslate.lean

import Mathlib
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AutomorphicForm MeasureTheory

theorem AutomorphicForm.constantTerm_rightTranslate
    {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    (μ : MeasureTheory.Measure Q) (u : Q → G) (f : G → ℂ) (g h : G) :
    AutomorphicForm.constantTerm μ u (fun x => f (x * h)) g
      = AutomorphicForm.constantTerm μ u f (g * h) := by sorry
