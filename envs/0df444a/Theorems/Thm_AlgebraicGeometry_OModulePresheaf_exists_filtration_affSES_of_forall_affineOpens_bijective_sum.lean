-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_filtration_affSES_of_forall_affineOpens_bijective_sum
-- name    : AlgebraicGeometry.OModulePresheaf.exists_filtration_affSES_of_forall_affineOpens_bijective_sum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/55889ffc-695c-54b8-8408-fc3d637260fa
-- title:
--   Filtration by affine-exact sequences from a direct-sum decomposition
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme and $\pi : V \to \operatorname{Spec} R$ a morphism. Here an `OModulePresheaf` over $\pi$ consists of a type $M(U)$ for each open $U \subseteq V$, carrying an abelian group structure, an $R$-module structure and a $\Gamma(V,U)$-module structure compatible with the $R$-algebra structure on $\Gamma(V,U)$ induced by $\pi$, together with $R$-linear restriction maps $M(U') \to M(U)$ for $U \le U'$ which are semilinear for restriction of functions and satisfy the usual identity and composition laws. Given such data $E$, a positive natural number $d$, a family $F : \mathbb{N} \to$ `OModulePresheaf` $\pi$, and for each $j \in \mathbb{N}$ a morphism $\iota_j : F_j \to E$ (a family of $R$-linear maps on all opens, semilinear for multiplication by sections and commuting with restriction), assume that for every affine open $U$ of $V$ the map $\prod_{j \in \mathrm{Fin}\,d} F_j(U) \to E(U)$, $s \mapsto \sum_{j < d} \iota_j(s_j)$, is bijective as a function. Then there is a family $P : \mathbb{N} \to$ `OModulePresheaf` $\pi$ with $P_0$ equal to the zero datum (all values a one-point type), $P_d$ equal to $E$, and such that for every $j < d$ there exists an `AffSES` $(P_j, P_{j+1}, F_j)$: morphisms defined on affine opens only, $P_j \to P_{j+1} \to F_j$, with the first injective, the second surjective, and range equal to kernel, on every affine open. No condition is imposed on $P_j$ for $j > d$.
--
--   This is a dévissage step: a pointwise direct-sum decomposition of presheaf-of-modules data over affine opens is converted into a filtration whose successive quotients are the summands, exact on affine opens. It is used in the construction of affine-exact filtrations for the pushforward data attached to multiplication by $n$ on an abelian scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_filtration_affSES_of_forall_affineOpens_bijective_sum.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_filtration_affSES_of_forall_affineOpens_bijective_sum
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (E : OModulePresheaf π) (d : ℕ) (hd : 0 < d) (F : ℕ → OModulePresheaf π)
    (ι : ∀ j : ℕ, OModulePresheaf.Hom (F j) E)
    (h : ∀ U : V.affineOpens, Function.Bijective
      (fun s : (j : Fin d) → (F j).obj U.1 => ∑ j : Fin d, (ι j).app U.1 (s j))) :
    ∃ P : ℕ → OModulePresheaf π,
      P 0 = OModulePresheaf.zero π ∧ P d = E ∧
      ∀ j : ℕ, j < d → Nonempty (OModulePresheaf.AffSES (P j) (P (j + 1)) (F j)) := by sorry
