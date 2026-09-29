-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_affine_weilRestriction_forall_existsUnique
-- name    : AlgebraicGeometry.exists_affine_weilRestriction_forall_existsUnique
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/caff09eb-e477-5396-b3f4-78c43b882b12
-- title:
--   Weil restriction of an affine finite-type scheme along a finite free extension
-- statement:
--   Let $R$ be a commutative ring, $R'$ a commutative $R$-algebra that is finite and free as an $R$-module, and $H$ a commutative $R'$-algebra of finite type. The assertion is the existence of a type $W$ carrying a commutative ring structure and an $R$-algebra structure, such that $W$ is of finite type over $R$, together with a morphism of schemes
--   $$\upsilon : \operatorname{Spec} R' \times_{\operatorname{Spec} R} \operatorname{Spec} W \longrightarrow \operatorname{Spec} H,$$
--   the fibre product being taken over the morphisms $\operatorname{Spec}$ of $R \to R'$ and of $R \to W$, with the following two properties. First, $\upsilon$ followed by $\operatorname{Spec}(R' \to H)$ equals the first projection of the fibre product, so that $\upsilon$ is a morphism over $\operatorname{Spec} R'$. Secondly, for every scheme $T$, every morphism $t : T \to \operatorname{Spec} R$, and every morphism $y : \operatorname{Spec} R' \times_{\operatorname{Spec} R} T \to \operatorname{Spec} H$ satisfying $y$ followed by $\operatorname{Spec}(R' \to H)$ equals the first projection (that is, $y$ is a morphism over $\operatorname{Spec} R'$), there is exactly one morphism $x : T \to \operatorname{Spec} W$ with $x$ followed by $\operatorname{Spec}(R \to W)$ equal to $t$, such that the base change of $x$ along $\operatorname{Spec} R' \to \operatorname{Spec} R$ — the morphism into $\operatorname{Spec} R' \times_{\operatorname{Spec} R} \operatorname{Spec} W$ induced by the first projection and by the second projection followed by $x$ — composed with $\upsilon$ equals $y$.
--
--   This is the existence and universal property of the Weil restriction $\operatorname{Res}_{R'/R}$ of an affine $R'$-scheme of finite type along a finite free extension $R \to R'$, in the strong form in which the representing affine $R$-scheme $\operatorname{Spec} W$ represents the restricted point functor on all $R$-schemes $T$, not merely on affine ones. It is deduced from the corresponding statement on algebras, [`Algebra.exists_weilRestriction_points_equiv_finiteType`](thm.html#Algebra.exists_weilRestriction_points_equiv_finiteType), and is used in the construction of solution schemes for the relative group law on Jacobians of curves with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_affine_weilRestriction_forall_existsUnique.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.exists_affine_weilRestriction_forall_existsUnique
    (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Module.Free R R']
    (H : Type u) [CommRing H] [Algebra R' H] [Algebra.FiniteType R' H] :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra R W), Algebra.FiniteType R W ∧
      ∃ υ : pullback (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R W))) ⟶
          Spec (CommRingCat.of H),
        υ ≫ Spec.map (CommRingCat.ofHom (algebraMap R' H)) = pullback.fst _ _ ∧
        ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R))
          (y : SchemeHomOver (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R'))) t)
            (Spec.map (CommRingCat.ofHom (algebraMap R' H)))),
          ∃! x : SchemeHomOver t (Spec.map (CommRingCat.ofHom (algebraMap R W))),
            pullback.lift (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R'))) t)
                (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R R'))) t ≫ x.1)
                (by rw [Category.assoc, x.2, pullback.condition]) ≫ υ = y.1 := by sorry
