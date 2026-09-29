-- Prove2me | Theorems.Thm_AutomorphicForm_isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport
-- name    : AutomorphicForm.isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/8194ae0e-1aa9-5bfe-8790-ac9ac82cffa5
-- title:
--   Right convolution preserves finite test factors
-- statement:
--   Let $F$ be a number field (a field of type `Type` equipped with the `NumberField` structure), let the group $G = GL_2(\mathbb{A}_F^{\mathrm{f}})$ of invertible $2\times 2$ matrices over the finite adele ring of $F$ carry a measurable space structure, and let $\mu$ be an arbitrary measure on $G$. Let $ff, g : G \to \mathbb{C}$ be functions, and assume that $ff$ satisfies `IsFinTestFactor F`, i.e. $ff$ is locally constant and has compact support (its topological support, the closure of $\{x : ff(x) \neq 0\}$, is compact), and that $g$ has compact support in the same sense. The conclusion is that the function
--   $$x \longmapsto \int_G ff(xb)\, g(b)\, d\mu(b)$$
--   again satisfies `IsFinTestFactor F`: it is locally constant and compactly supported. No integrability, measurability or invariance hypotheses on $\mu$, and no hypothesis beyond compact support on $g$, are imposed.
--
--   This is the finite-adelic half of the statement that a right convolution of factorisable test functions is again factorisable, the local constancy and compact support of a finite Hecke-algebra element being preserved under convolution against a compactly supported weight. It is used in the construction of a factorisable test function with prescribed behaviour attached to a cuspidal constituent, via [`AutomorphicForm.CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_rightConv_comp_inv`](thm.html#AutomorphicForm.CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_rightConv_comp_inv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport.lean

import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory AutomorphicForm

theorem AutomorphicForm.isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))]
    (μ : Measure (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)))
    (ff g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ)
    (hff : IsFinTestFactor F ff) (hgs : HasCompactSupport g) :
    IsFinTestFactor F (fun x => ∫ b, ff (x * b) * g b ∂μ) := by sorry
