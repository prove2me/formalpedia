-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffSES_injective_inc_HSuccMap_of_forall_subsingleton_HSucc_of_surjective_proj_H0Map
-- name    : AlgebraicGeometry.OModulePresheaf.AffSES.injective_inc_HSuccMap_of_forall_subsingleton_HSucc_of_surjective_proj_H0Map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/f3ca275d-d3de-5006-b7ad-8463a513065e
-- title:
--   Injectivity of check H^*(mathcal F₁)→check H^*(mathcal F₂) when check H^{>0}(mathcal F₃) vanishes
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme and $\pi : V \to \operatorname{Spec} R$ a separated morphism, and let $F_1, F_2, F_3$ be data of type `OModulePresheaf π`, i.e. assignments $U \mapsto F(U)$ on the opens of $V$ carrying compatible $R$- and $\Gamma(V,U)$-module structures together with $R$-linear restriction maps satisfying the semilinearity, reflexivity and transitivity laws. Let $S$ be an `AffSES F₁ F₂ F₃`: a pair of morphisms $\mathrm{inc} : F_1 \to F_2$ and $\mathrm{proj} : F_2 \to F_3$, each given by $\Gamma(V,U)$-semilinear maps on affine opens commuting with restriction, such that for every affine open $U$ of $V$ the map $\mathrm{inc}$ on $U$ is injective, the map $\mathrm{proj}$ on $U$ is surjective, and the range of the first equals the kernel of the second. Let $K$ be an ordered affine cover of $V$: a finite linearly ordered index type together with affine opens $U_i$ whose supremum is $\top$. Assume that for every $i \in \mathbb N$ the module $F_3.\mathrm{HSucc}\,K\,i = \ker(d^{i+1}) / \operatorname{im}(d^{i})$ of the Čech complex of $F_3$ for $K$ is a subsingleton, and that the map induced by $\mathrm{proj}$ on degree-zero Čech cocycles, $F_2.\mathrm{H0}\,K \to F_3.\mathrm{H0}\,K$, is surjective. Then for every $i \in \mathbb N$ the induced map $F_1.\mathrm{HSucc}\,K\,i \to F_2.\mathrm{HSucc}\,K\,i$ on the $(i+1)$-st Čech cohomology is injective.
--
--   This is the injectivity half of the long exact Čech cohomology sequence attached to a short exact sequence of module data which is exact on affine opens, in the shape needed when the quotient term has vanishing higher Čech cohomology. It is used in the cohomological regularity induction for twists of closed subschemes of projective space, via [`AlgebraicGeometry.ProjSpace.forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_maximal_growth`](thm.html#AlgebraicGeometry.ProjSpace.forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_maximal_growth).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_AffSES_injective_inc_HSuccMap_of_forall_subsingleton_HSucc_of_surjective_proj_H0Map.lean

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Noetherian.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.AffSES.injective_inc_HSuccMap_of_forall_subsingleton_HSucc_of_surjective_proj_H0Map
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsSeparated π]
    {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (K : V.OrderedAffineCover)
    (h₃ : ∀ i : ℕ, Subsingleton (F₃.HSucc K i))
    (hsurj : Function.Surjective (S.proj.H0Map K)) :
    ∀ i : ℕ, Function.Injective (S.inc.HSuccMap K i) := by sorry
