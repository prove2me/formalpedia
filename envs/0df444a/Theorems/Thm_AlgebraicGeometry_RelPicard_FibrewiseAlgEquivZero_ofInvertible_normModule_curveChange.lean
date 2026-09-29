-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_FibrewiseAlgEquivZero_ofInvertible_normModule_curveChange
-- name    : AlgebraicGeometry.RelPicard.FibrewiseAlgEquivZero.ofInvertible_normModule_curveChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/eff98c27-ca75-5e01-9265-9f7c0a1b1118
-- title:
--   Norms preserve fibrewise algebraic triviality of line bundles
-- statement:
--   Let $R$ be a commutative ring, let $c : C \to \operatorname{Spec} R$ and $c' : C' \to \operatorname{Spec} R$ be schemes over $R$, and let $\varepsilon$ be a section of $c$, that is, a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Let $\pi : C' \to C$ satisfy $\pi$ followed by $c$ equals $c'$, and be finite, flat and locally of finite presentation, with $\pi.\mathrm{finrank}\,y = d$ at every point $y$ of $C$ for a fixed $d \in \mathbb{N}$. Let $t : T \to \operatorname{Spec} R$ be a further $R$-scheme and let $L'$ be an invertible module on $C' \times_R T$ (invertibility in the sense that every point has an open neighbourhood $U$ on which the restriction of $L'$ is isomorphic to the unit module of $U$). Assume that $L'$ is fibrewise algebraically equivalent to zero: for every algebraically closed field $k$ and every $s : \operatorname{Spec} k \to T$, the pullback of $L'$ to $(C' \times_R T) \times_T \operatorname{Spec} k$ admits a witness of `IsAlgEquivZero` over the structure morphism of that fibre, namely a scheme $T'$ with a locally of finite type, geometrically integral morphism $h : T' \to \operatorname{Spec} k$, an invertible module $M$ on the fibre fibred over $T'$, and two sections $t_0, t_1$ of $h$ such that the restriction of $M$ at $t_0$ is isomorphic to the unit module and its restriction at $t_1$ is isomorphic to the pullback of the given bundle. Assume finally that the norm module $\det_d(\pi_{T*}L') \otimes (\det_d(\pi_{T*}\mathcal{O}))^{\vee}$ on $C \times_R T$, formed along the base change $\pi_T =$ `curveChange π hπ t` of $\pi$ to $T$ and the rank $d$, is invertible. Then the rigidified line bundle on $C \times_R T$ obtained from this norm module by `RigidifiedLineBundle.ofInvertible`, whose underlying module is the norm tensored with the pullback along $C \times_R T \to T$ of the dual of its restriction along the rigidifying section determined by $\varepsilon$, is itself fibrewise algebraically equivalent to zero in the same sense, over every algebraically closed field $k$ and every $s : \operatorname{Spec} k \to T$.
--
--   This is the statement that the norm along a finite locally free morphism of constant rank carries the degree-zero part of the relative Picard functor of $C'$ into that of $C$: it verifies the $\mathrm{Pic}^0$ condition for the rigidified norm bundle. It is used in the construction of the norm homomorphism between relative $\mathrm{Pic}^0$ functors and in the comparison of that homomorphism with the Abel–Jacobi map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_FibrewiseAlgEquivZero_ofInvertible_normModule_curveChange.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.RelPicard

universe u

set_option maxHeartbeats 800000 in

theorem AlgebraicGeometry.RelPicard.FibrewiseAlgEquivZero.ofInvertible_normModule_curveChange
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    (π : C' ⟶ C) (hπ : π ≫ c = c') [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ y : C, π.finrank y = d)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (L' : (Limits.pullback c' t).Modules)
    (hL' : Scheme.Modules.IsInvertible L')
    (hfae : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      IsAlgEquivZero (fibreAt c' t s)
        ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd c' t) s)).obj L'))
    (hinv : Scheme.Modules.IsInvertible (Scheme.Modules.normModule (curveChange π hπ t) d L')) :
    FibrewiseAlgEquivZero (RigidifiedLineBundle.ofInvertible (ε := ε) _ hinv) := by sorry
