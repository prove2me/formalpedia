-- Prove2me | Theorems.Thm_AutomorphicForm_constantTerm_add
-- name    : AutomorphicForm.constantTerm_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/0630f118-2bad-5ff1-931c-5e11054a06f7
-- title:
--   Additivity of the constant-term integral
-- statement:
--   Let $Q$ be a type with a measurable space structure, $G$ a group, $\mu$ a measure on $Q$, and $u : Q \to G$ an arbitrary function. Let $f_1, f_2 : G \to \mathbb{C}$ and let $g \in G$. Here [`AutomorphicForm.constantTermIntegrand u f g`](def/AutomorphicForm_ConstantTerm.html#L44) denotes the function $q \mapsto f(u(q)\,g)$ on $Q$, and [`AutomorphicForm.constantTerm μ u f g`](def/AutomorphicForm_ConstantTerm.html#L47) denotes its Bochner integral $\int_Q f(u(q)\,g)\,d\mu(q)$. Assume that the two integrands $q \mapsto f_1(u(q)\,g)$ and $q \mapsto f_2(u(q)\,g)$ are $\mu$-integrable. The conclusion is that the constant term of the pointwise sum $x \mapsto f_1(x) + f_2(x)$ at $g$ equals the sum of the constant terms of $f_1$ and $f_2$ at $g$, that is,
--   $$\int_Q \bigl(f_1(u(q)g) + f_2(u(q)g)\bigr)\,d\mu(q) = \int_Q f_1(u(q)g)\,d\mu(q) + \int_Q f_2(u(q)g)\,d\mu(q).$$
--   No measurability or continuity hypothesis on $u$, and no group-theoretic hypothesis relating $u$ to a unipotent subgroup, is required: the statement is pure additivity of an integral along the map $q \mapsto u(q)g$.
--
--   This is the additivity half of the linearity of the constant-term (unipotent period) operator attached to a parametrisation $u$ of a group by a measure space, in the shape needed to recognise cuspidality conditions as linear. It is used for the closure of the cuspidality predicate under addition, via [`AutomorphicForm.IsCuspidalFn.add`](thm.html#AutomorphicForm.IsCuspidalFn.add), and in the additivity of the twisted adelic kernel decomposition [`AutomorphicForm.forall_exists_lambdaT_twistedAdelicKernel_eq_finsum_add_sub_indicator_constantTerm_add`](thm.html#AutomorphicForm.forall_exists_lambdaT_twistedAdelicKernel_eq_finsum_add_sub_indicator_constantTerm_add).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_constantTerm_add.lean

import Mathlib
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AutomorphicForm MeasureTheory

theorem AutomorphicForm.constantTerm_add
    {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    (μ : MeasureTheory.Measure Q) (u : Q → G) {f₁ f₂ : G → ℂ} (g : G)
    (h₁ : MeasureTheory.Integrable (AutomorphicForm.constantTermIntegrand u f₁ g) μ)
    (h₂ : MeasureTheory.Integrable (AutomorphicForm.constantTermIntegrand u f₂ g) μ) :
    AutomorphicForm.constantTerm μ u (fun x => f₁ x + f₂ x) g
      = AutomorphicForm.constantTerm μ u f₁ g + AutomorphicForm.constantTerm μ u f₂ g := by sorry
