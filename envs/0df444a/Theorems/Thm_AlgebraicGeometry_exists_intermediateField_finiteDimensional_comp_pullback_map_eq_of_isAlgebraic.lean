-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_intermediateField_finiteDimensional_comp_pullback_map_eq_of_isAlgebraic
-- name    : AlgebraicGeometry.exists_intermediateField_finiteDimensional_comp_pullback_map_eq_of_isAlgebraic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/f910075b-201e-550e-9756-da1c73c02076
-- title:
--   Morphisms over an algebraic extension descend to a finite subextension
-- statement:
--   Let $K/k$ be an algebraic extension of fields, and let $X$ and $Y$ be schemes (in the zeroth universe) equipped with morphisms $f_X : X \to \operatorname{Spec} k$ and $f_Y : Y \to \operatorname{Spec} k$, where the underlying space of $X$ is compact and quasi-separated and $f_Y$ is locally of finite type. Write $X_K$ and $Y_K$ for the pullbacks of $f_X$, resp. $f_Y$, along $\operatorname{Spec} K \to \operatorname{Spec} k$, and similarly $X_L, Y_L$ for an intermediate field $L$. Let $f : X_K \to Y_K$ be a morphism commuting with the second projections to $\operatorname{Spec} K$, that is, a morphism of $K$-schemes. Then there exist an intermediate field $k \subseteq L \subseteq K$ with $L$ finite-dimensional over $k$, a morphism $g : X_L \to Y_L$, and the identification of $\operatorname{Spec} K \to \operatorname{Spec} L \to \operatorname{Spec} k$ with $\operatorname{Spec} K \to \operatorname{Spec} k$ (exported as an equation $h\iota$ so that the comparison morphisms can be formed), such that $g$ commutes with the second projections to $\operatorname{Spec} L$, and such that the square formed by $f$, $g$ and the canonical morphisms $X_K \to X_L$, $Y_K \to Y_L$ induced by $\mathrm{id}_X$, $\mathrm{id}_Y$ and $\operatorname{Spec} K \to \operatorname{Spec} L$ commutes.
--
--   This is the schematic limit argument of EGA IV 8.13.1 in the special case of the filtered system of finite subextensions of an algebraic extension: since the projection square is cartesian, the commuting square asserted here says that $f$ is the base change of the $L$-morphism $g$. It is used to descend Galois twists and group actions to finite levels, and is cited in the pullback-square reformulation, in the existence of a finite Galois subextension carrying a given twist, and in the construction of torsion data on fake elliptic curves in the Cerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_intermediateField_finiteDimensional_comp_pullback_map_eq_of_isAlgebraic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_intermediateField_finiteDimensional_comp_pullback_map_eq_of_isAlgebraic
    (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (X Y : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [QuasiSeparatedSpace X] [LocallyOfFiniteType fY]
    (f : pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ pullback fY (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hf : f ≫ pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    ∃ (L : IntermediateField k K) (_ : FiniteDimensional k L)
      (g : pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶ pullback fY (Spec.map (CommRingCat.ofHom (algebraMap k L))))

      (hι : Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) =
        Spec.map (CommRingCat.ofHom (algebraMap k K))),

      g ≫ pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
        pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) ∧

      f ≫ pullback.map fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k L)))
            (𝟙 Y) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) =
        pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fX (Spec.map (CommRingCat.ofHom (algebraMap k L)))
            (𝟙 X) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) ≫ g := by sorry
