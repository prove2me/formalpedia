-- Prove2me | Theorems.Thm_AutomorphicForm_constantTerm_smul
-- name    : AutomorphicForm.constantTerm_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/04c77660-2a75-57a8-8cad-96735a10af8b
-- title:
--   Homogeneity of the constant term in the function
-- statement:
--   Let $Q$ be a measurable space and $G$ a group, let $\mu$ be a measure on $Q$, let $u : Q \to G$ be an arbitrary function, let $c \in \mathbb{C}$, let $f : G \to \mathbb{C}$ be an arbitrary function and let $g \in G$. Here [`AutomorphicForm.constantTerm`](def/AutomorphicForm_ConstantTerm.html#L47) $\mu$ $u$ $f$ $g$ denotes the Bochner integral $\int_Q f(u(q)\,g)\,d\mu(q)$, i.e. the integral over $Q$ of the integrand $q \mapsto f(u(q)g)$ obtained by translating $f$ on the right by $g$ and pulling back along $u$. The assertion is that replacing $f$ by the pointwise scaled function $x \mapsto c\,f(x)$ multiplies this integral by $c$: $$\int_Q c\,f(u(q)\,g)\,d\mu(q) = c\int_Q f(u(q)\,g)\,d\mu(q).$$ No measurability of $u$ or $f$ and no integrability of the integrand is assumed; the identity holds for the Bochner integral in all cases, both sides being $0$ when the integrand fails to be integrable. The group $G$ carries no topology or measurable structure here, and $\mu$ is an arbitrary measure, not assumed Haar or finite.
--
--   This is the homogeneity half of the linearity of the constant-term operator $f \mapsto \bigl(g \mapsto \int_Q f(u(q)g)\,d\mu(q)\bigr)$ in its function argument, stated for the abstract situation of a measure space $Q$ mapping into a group $G$. It is used by [`AutomorphicForm.IsCuspidalFn.smul`](thm.html#AutomorphicForm.IsCuspidalFn.smul), that is, in exhibiting the functions with vanishing constant term as a $\mathbb{C}$-submodule.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_constantTerm_smul.lean

import Mathlib
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AutomorphicForm MeasureTheory

theorem AutomorphicForm.constantTerm_smul
    {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    (μ : MeasureTheory.Measure Q) (u : Q → G) (c : ℂ) (f : G → ℂ) (g : G) :
    AutomorphicForm.constantTerm μ u (fun x => c * f x) g
      = c * AutomorphicForm.constantTerm μ u f g := by sorry
