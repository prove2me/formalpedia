-- Prove2me | Theorems.Thm_AutomorphicForm_isFactorizableTestFn_sum_mul_comp_mul_mul
-- name    : AutomorphicForm.isFactorizableTestFn_sum_mul_comp_mul_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/bd4675c3-e26b-5313-8580-fc5b37259419
-- title:
--   Finite sums of archimedean two-sided translates stay factorizable
-- statement:
--   Let $F$ be a number field, and let $f$ be a complex-valued function on $\mathrm{GL}_2$ of the adele ring of $F$ which is a factorizable test function in the sense of the project: there are functions $f_\infty$ on $\mathrm{GL}_2$ of the infinite adeles and $f_{\mathrm{f}}$ on $\mathrm{GL}_2$ of the finite adeles such that $f_\infty$ is of the form $\Phi \circ \mathrm{archEntries}_F$ for some $\Phi$ on the $2\times 2$ matrices over the mixed space of $F$ that is $C^\infty$ over $\mathbb{R}$ and $f_\infty$ has compact support, $f_{\mathrm{f}}$ is locally constant with compact support, and $f(g) = f_\infty(\mathrm{glArch}\,g)\cdot f_{\mathrm{f}}(\mathrm{glFin}\,g)$ for all $g$, where $\mathrm{glArch}$ and $\mathrm{glFin}$ are the maps on $\mathrm{GL}_2$ induced by the projections of the adeles onto the infinite and the finite adeles. Let $n \in \mathbb{N}$, let $c : \mathrm{Fin}\,n \to \mathbb{C}$ be scalars, and let $a, b : \mathrm{Fin}\,n \to \mathrm{GL}_2(\mathbb{A}_F)$ be such that every $a_i$ and every $b_i$ lies in the supremum, over the infinite places $w$ of $F$, of the ranges of the homomorphisms `rowIsometryInclAt₀ F w`. Then the function $y \mapsto \sum_i c_i\, f(a_i\, y\, b_i)$ is again a factorizable test function in the same sense.
--
--   Factorizable (pure tensor) test functions are the functions used to build the convolution operators acting on adelic automorphic forms; this closure property says that the span of such functions is stable under finite linear combinations of two-sided translates by elements of the archimedean row-isometry subgroups. It is used in the construction of the archimedean cut-off projectors, through [`AutomorphicForm.exists_rightConv_eq_of_archCutProjector`](thm.html#AutomorphicForm.exists_rightConv_eq_of_archCutProjector).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isFactorizableTestFn_sum_mul_comp_mul_mul.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm AutomorphicForm.CuspidalConstituent
open scoped BigOperators

theorem AutomorphicForm.isFactorizableTestFn_sum_mul_comp_mul_mul
    (F : Type) [Field F] [NumberField F]
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsFactorizableTestFn F f) {n : ℕ} (c : Fin n → ℂ)
    (a b : Fin n → AdelicGL2 (𝓞 F) F)
    (ha : ∀ i, a i ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range))
    (hb : ∀ i, b i ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range)) :
    IsFactorizableTestFn F (fun y => ∑ i, c i * f (a i * y * b i)) := by sorry
