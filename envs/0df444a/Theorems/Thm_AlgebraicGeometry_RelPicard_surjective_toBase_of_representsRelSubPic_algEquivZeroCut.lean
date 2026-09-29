-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_surjective_toBase_of_representsRelSubPic_algEquivZeroCut
-- name    : AlgebraicGeometry.RelPicard.surjective_toBase_of_representsRelSubPic_algEquivZeroCut
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/d1b376aa-176f-5991-845c-cb5bb3ec5dcf
-- title:
--   Surjectivity of the structure morphism of a relative Pic⁰ representing scheme
-- statement:
--   Let $R$ be a commutative ring, let $c \colon C \to \operatorname{Spec} R$ be a morphism of schemes, and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Let $D$ be a relative $\mathrm{Pic}^0$ designation for $c$: a scheme $D.P$ together with a structure morphism $D.\mathrm{toBase} \colon D.P \to \operatorname{Spec} R$, a morphism $D.\mathrm{zeroSection} \colon \operatorname{Spec} R \to D.P$, and the identity $D.\mathrm{zeroSection}$ followed by $D.\mathrm{toBase}$ equals $\mathrm{id}_{\operatorname{Spec} R}$. Assume $h$: $D$ represents, in the sense of `RepresentsRelSubPic`, the subcondition `algEquivZeroCut c ε` of the rigidified relative Picard functor of $(c,\varepsilon)$, whose predicate on a rigidified line bundle $M$ over a base $t \colon T \to \operatorname{Spec} R$ is `FibrewiseAlgEquivZero M`: for every algebraically closed field $k$ and every $s \colon \operatorname{Spec} k \to T$, the pullback of $M.L$ to the corresponding geometric fibre satisfies the predicate `IsAlgEquivZero`; representability means a rigidified Poincaré bundle over $D.\mathrm{toBase}$ satisfying the condition, the usual universal property up to isomorphism of the underlying invertible modules, and triviality of its pullback along the zero section. The conclusion is that $D.\mathrm{toBase}$ is a surjective morphism of schemes.
--
--   This is the elementary observation that a morphism admitting a section is surjective, applied to the structure morphism of a scheme representing the algebraic-equivalence-to-zero part of the rigidified relative Picard functor. It is one of the standing conjuncts verified when such a representing object is produced, and is invoked by the existence statements [`AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_chartData`](thm.html#AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_chartData) and the two base-change variants away from finitely many primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_surjective_toBase_of_representsRelSubPic_algEquivZeroCut.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.surjective_toBase_of_representsRelSubPic_algEquivZeroCut
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) :
    Surjective D.toBase := by sorry
