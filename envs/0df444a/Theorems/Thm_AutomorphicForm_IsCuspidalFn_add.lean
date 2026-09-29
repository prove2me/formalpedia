-- Prove2me | Theorems.Thm_AutomorphicForm_IsCuspidalFn_add
-- name    : AutomorphicForm.IsCuspidalFn.add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/69813909-8b10-5635-bda6-3c98d13d3663
-- title:
--   Additivity of cuspidality for integrable constant-term integrands
-- statement:
--   Let $Q$ be a measurable space carrying a measure $\mu$, let $G$ be a group, let $u : Q \to G$ be a map, and let $f_1, f_2 : G \to \mathbb{C}$. For a function $f$ and a point $g \in G$, the constant-term integrand `constantTermIntegrand u f g` is the function $q \mapsto f(u(q)\,g)$ on $Q$, its constant term `constantTerm` at $g$ is the Bochner integral $\int_Q f(u(q)\,g)\,d\mu(q)$, and `IsCuspidalFn` asserts that this integral vanishes for every $g \in G$. Assume that $f_1$ and $f_2$ are cuspidal in this sense, i.e. $\int_Q f_i(u(q)\,g)\,d\mu(q) = 0$ for all $g \in G$ and $i = 1,2$, and assume that for every $g \in G$ both integrands $q \mapsto f_1(u(q)\,g)$ and $q \mapsto f_2(u(q)\,g)$ are $\mu$-integrable. Then the pointwise sum $x \mapsto f_1(x) + f_2(x)$ is again cuspidal: its constant term vanishes at every $g \in G$. No continuity, measurability or automorphy conditions on $f_1$, $f_2$ or $u$ beyond the stated integrability are required.
--
--   This is the additivity half of the statement that the cuspidal functions, among those whose constant-term integrands are everywhere integrable, form a linear subspace; together with the corresponding compatibility with scalar multiplication it underlies the construction of the cuspidal subspace used in the Langlands–Tunnell part of the development. It is cited in the construction of archimedean Casimir eigenvectors of minimal weight in a continuous realisation, and in the argument producing a nonzero vector in an intersection of an isotypic cuspidal submodule with an archimedean cut submodule.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_IsCuspidalFn_add.lean

import Mathlib
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AutomorphicForm MeasureTheory

theorem AutomorphicForm.IsCuspidalFn.add
    {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    {μ : MeasureTheory.Measure Q} {u : Q → G} {f₁ f₂ : G → ℂ}
    (hf₁ : AutomorphicForm.IsCuspidalFn μ u f₁) (hf₂ : AutomorphicForm.IsCuspidalFn μ u f₂)
    (h₁ : ∀ g, MeasureTheory.Integrable (AutomorphicForm.constantTermIntegrand u f₁ g) μ)
    (h₂ : ∀ g, MeasureTheory.Integrable (AutomorphicForm.constantTermIntegrand u f₂ g) μ) :
    AutomorphicForm.IsCuspidalFn μ u (fun x => f₁ x + f₂ x) := by sorry
