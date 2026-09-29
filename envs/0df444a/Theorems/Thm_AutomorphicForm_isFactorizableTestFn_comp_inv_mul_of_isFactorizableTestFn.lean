-- Prove2me | Theorems.Thm_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn
-- name    : AutomorphicForm.isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/846f60fa-b8b2-560a-ae97-9c812e7b0e60
-- title:
--   Factorizable test functions are stable under left translation
-- statement:
--   Let $K$ be a number field (a field with the `NumberField` instance, so with ring of integers $\mathcal{O}_K$), let $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be a function on the general linear group of degree $2$ over the adele ring of $K$, and let $t \in \mathrm{GL}_2(\mathbb{A}_K)$ be arbitrary (no condition is imposed on $t$). Assume `IsFactorizableTestFn K f`, that is: there are functions $f_a$ on $\mathrm{GL}_2$ of the infinite adele ring of $K$ and $f_f$ on $\mathrm{GL}_2$ of the finite adele ring of $\mathcal{O}_K$ in $K$ such that (i) $f_a$ has compact support and is given by a map of its matrix entries, i.e. there is a function $\Phi$ on $2 \times 2$ matrices over the mixed space of $K$ which is $C^\infty$ over $\mathbb{R}$ with $f_a(g) = \Phi(\mathrm{archEntries}\,K\,g)$ for all $g$; (ii) $f_f$ is locally constant with compact support; and (iii) $f(g) = f_a(\mathrm{glArch}(g)) \cdot f_f(\mathrm{glFin}(g))$ for all $g$, where `glArch` and `glFin` are the group homomorphisms induced on $\mathrm{GL}_2$ by the archimedean and finite projections of the adele ring. The conclusion is that the function $y \mapsto f(t^{-1} y)$ again satisfies `IsFactorizableTestFn K`.
--
--   This is the stability of the space of pure-tensor test functions on $\mathrm{GL}_2(\mathbb{A}_K)$ under the left translation operators, the elementary bookkeeping that makes the left regular action available on this space. It is used throughout the analytic part of the development, for instance in the construction of test data for Rankin–Selberg integrals and in the class-sum growth estimates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn.lean

import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField

theorem AutomorphicForm.isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn
    (K : Type) [Field K] [NumberField K]
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (hf : IsFactorizableTestFn K f)
    (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    IsFactorizableTestFn K (fun y => f (t⁻¹ * y)) := by sorry
