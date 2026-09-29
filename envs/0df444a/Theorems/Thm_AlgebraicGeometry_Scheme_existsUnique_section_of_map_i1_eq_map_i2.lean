-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_section_of_map_i1_eq_map_i2
-- name    : AlgebraicGeometry.Scheme.existsUnique_section_of_map_i1_eq_map_i2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/4e0ba9b9-212f-5a22-952a-fbb47176a4ff
-- title:
--   Descent of fppf sheaf sections along faithfully flat algebras
-- statement:
--   Let $E$ be a sheaf of abelian groups on the big fppf site of schemes, that is, a sheaf for `Scheme.fppfTopology` in universe $u$ with values in `AddCommGrpCat.{u+1}`, and write $E.obj$ for its underlying presheaf on the opposite category of schemes. Let $R$ and $A$ be commutative rings in `Type u`, with $A$ an $R$-algebra which is faithfully flat as an $R$-module and of finite presentation as an $R$-algebra. Let $e$ be an element of the underlying type of the abelian group $E(\operatorname{Spec} A)$, and assume that the two pull-backs of $e$ to $E(\operatorname{Spec}(A \otimes_R A))$ agree, namely along $\operatorname{Spec}$ of the two coface maps `i₁ R A` and `i₂ R A`, which are the ring homomorphisms $A \to A \otimes_R A$ given by $a \mapsto a \otimes 1$ and $a \mapsto 1 \otimes a$. Then there is exactly one element $e_0$ of $E(\operatorname{Spec} R)$ whose pull-back along $\operatorname{Spec}$ of the structure morphism $R \to A$ equals $e$.
--
--   This is the sheaf axiom for an fppf sheaf of abelian groups, made explicit for the single affine covering $\operatorname{Spec} A \to \operatorname{Spec} R$ attached to a faithfully flat finitely presented algebra: Amitsur-style descent of sections along $R \to A$. It is used by [`AlgebraicGeometry.exists_section_of_fppfAmitsurTrivial`](thm.html#AlgebraicGeometry.exists_section_of_fppfAmitsurTrivial).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_existsUnique_section_of_map_i1_eq_map_i2.lean

import Mathlib
import Definitions.Def_Algebra_DescentCofaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry Algebra.DescentCofaces
open scoped TensorProduct

theorem AlgebraicGeometry.Scheme.existsUnique_section_of_map_i1_eq_map_i2
    (E : Sheaf Scheme.fppfTopology.{u} AddCommGrpCat.{u + 1})
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.FaithfullyFlat R A] [Algebra.FinitePresentation R A]
    (e : ToType (E.obj.obj (op (Spec (.of A)))))
    (he : E.obj.map (Spec.map (i₁ R A)).op e = E.obj.map (Spec.map (i₂ R A)).op e) :
    ∃! e₀ : ToType (E.obj.obj (op (Spec (.of R)))),
      E.obj.map (Spec.map (CommRingCat.ofHom (algebraMap R A))).op e₀ = e := by sorry
