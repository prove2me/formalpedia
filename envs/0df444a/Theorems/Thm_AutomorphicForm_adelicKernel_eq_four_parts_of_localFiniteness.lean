-- Prove2me | Theorems.Thm_AutomorphicForm_adelicKernel_eq_four_parts_of_localFiniteness
-- name    : AutomorphicForm.adelicKernel_eq_four_parts_of_localFiniteness
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/a2e01890-ac67-5d9a-b872-327b7a392995
-- title:
--   Four-cell decomposition of the adelic kernel
-- statement:
--   Let $F$ be a number field and $M$ an additive commutative monoid. Write $G(\mathbb{A}) = \mathrm{GL}_2(\mathbb{A}_F)$ for [`AutomorphicForm.AdelicGL2 (𝓞 F) F`](def/AutomorphicForm_AdelicLsXi.html#L12), the general linear group of $2\times 2$ matrices over the adele ring of $F$, and let $\iota =$ `globalPoints` denote the group homomorphism $\mathrm{GL}_2(F) \to G(\mathbb{A})$ induced entrywise by $F \to \mathbb{A}_F$. Assume the predicate [`AutomorphicForm.AdelicKernelLocalFiniteness F`](def/AutomorphicForm_AdelicKernel.html#L37), i.e. for every compact set $C' \subseteq G(\mathbb{A})$ and all $x, y \in G(\mathbb{A})$ the set $\{\gamma \in \mathrm{GL}_2(F) : x^{-1}\,\iota(\gamma)\,y \in C'\}$ is finite. Let $f : G(\mathbb{A}) \to M$, let $C \subseteq G(\mathbb{A})$ be compact with $\operatorname{supp} f \subseteq C$, and let $x, y \in G(\mathbb{A})$. Then the unconditional (finitely supported) sum $\sum^{\mathrm{f}}_{\gamma \in \mathrm{GL}_2(F)} f(x^{-1}\iota(\gamma)y)$ equals the sum of the four analogous sums taken over the subsets of $\mathrm{GL}_2(F)$ cut out by the predicates `IsCentralType`, `IsEllipticType`, `IsHyperbolicType` and `IsUnipotentType` applied to the underlying matrix of $\gamma$, added in that order.
--
--   This is the opening step of the geometric side of the $\mathrm{GL}_2$ trace formula: the sum over rational points defining the automorphic kernel is regrouped according to the conjugacy type of $\gamma$, here with no convergence hypothesis beyond compact support of $f$ and the stated local-finiteness property. It is used in the subsequent treatment of the central-plus-elliptic and parabolic (hyperbolic plus unipotent) contributions, in particular by the results isolating the truncated kernel and the integral of its parabolic part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_adelicKernel_eq_four_parts_of_localFiniteness.lean

import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_AdelicKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix

open scoped NumberField

theorem AutomorphicForm.adelicKernel_eq_four_parts_of_localFiniteness
    (F : Type) [Field F] [NumberField F] {M : Type*} [AddCommMonoid M]
    (h : AutomorphicForm.AdelicKernelLocalFiniteness F)
    {f : AutomorphicForm.AdelicGL2 (𝓞 F) F → M}
    {C : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)}
    (hC : IsCompact C) (hsupp : Function.support f ⊆ C)
    (x y : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
    AutomorphicForm.adelicKernel F f x y
      = AutomorphicForm.adelicKernelCentralPart F f x y
        + AutomorphicForm.adelicKernelEllipticPart F f x y
        + AutomorphicForm.adelicKernelHyperbolicPart F f x y
        + AutomorphicForm.adelicKernelUnipotentPart F f x y := by sorry
