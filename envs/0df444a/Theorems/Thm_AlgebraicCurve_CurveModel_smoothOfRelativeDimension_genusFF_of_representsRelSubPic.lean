-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_smoothOfRelativeDimension_genusFF_of_representsRelSubPic
-- name    : AlgebraicCurve.CurveModel.smoothOfRelativeDimension_genusFF_of_representsRelSubPic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/cd7b38b8-b804-5444-88bc-27122e5d070d
-- title:
--   Smoothness of relative dimension g for Pic⁰
-- statement:
--   Let $K$ be an algebraically closed field and let $F$ be a field equipped with a $K$-algebra structure which is a curve over $K$ in the sense of `IsCurveOver`: every nonzero $f \in F$ admits a divisor whose value at each place $v$ is $v.\mathrm{ord}(f)$ and whose degree is $0$, every place of $F/K$ has residue field finite-dimensional over $K$, and $\Omega[F/K]$ is free of rank one over $F$. Assume in addition that $F$ contains an element $x$ transcendental over $K$ with $F$ finite-dimensional over $K(x)$. Let $M$ be a model of $F$ over $K$ in the sense of `CurveModel`, that is an integral scheme $M.C$ with a proper morphism $M.\mathrm{toBase} : M.C \to \operatorname{Spec} K$ that is smooth of relative dimension $1$, a ring isomorphism of $F$ with the function field of $M.C$ compatible with the map of $K$ into the function field, a bijection between the closed points of $M.C$ and the places of $F/K$ identifying each stalk with the corresponding valuation subring, and the property that every finite set of points of $M.C$ lies in an affine open. Let $s$ be a section of $M.\mathrm{toBase}$, i.e. a morphism $\operatorname{Spec} K \to M.C$ composing with $M.\mathrm{toBase}$ to the identity, and let $D$ consist of a scheme $D.P$, a morphism $D.\mathrm{toBase} : D.P \to \operatorname{Spec} K$ and a section $D.\mathrm{zeroSection}$ of it. Suppose $D$ represents, via data `h`, the subfunctor of the $s$-rigidified relative Picard functor of $M.\mathrm{toBase}$ cut out by `algEquivZeroCut`: there is a rigidified invertible module (Poincaré bundle) on the pullback of $M.C$ along $D.\mathrm{toBase}$ whose restriction to every geometric fibre over an algebraically closed field is algebraically equivalent to zero, such that for every $K$-scheme $t : T \to \operatorname{Spec} K$ and every rigidified invertible module on $M.C \times_K T$ with the same fibrewise property there is a unique morphism $T \to D.P$ over $\operatorname{Spec} K$ pulling the Poincaré bundle back to it, and the pullback along $D.\mathrm{zeroSection}$ is isomorphic to the unit bundle. Then $D.\mathrm{toBase}$ is smooth of relative dimension $\mathrm{genusFF}\,K\,F$, the dimension over $K$ of $H^1$ of the zero divisor in the repartition complex of $F/K$.
--
--   This is the statement that the Jacobian of a smooth proper curve of genus $g$ over an algebraically closed field is smooth over the base of relative dimension $g$, here phrased for any scheme representing the algebraic-equivalence-to-zero part of the rigidified relative Picard functor of a model of the function field. It feeds into the study of the Jacobian's endomorphisms and Frobenius, being cited in the analysis of the resultant description of kernels of polynomials in the Frobenius on $\mathrm{Pic}^0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_smoothOfRelativeDimension_genusFF_of_representsRelSubPic.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicCurve

universe u v

theorem AlgebraicCurve.CurveModel.smoothOfRelativeDimension_genusFF_of_representsRelSubPic
    (K : Type u) [Field K] [IsAlgClosed K] (F : Type v) [Field F] [Algebra K F] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (M : CurveModel K F)
    (s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _})
    (D : RelativePic0Designation K M.toBase)
    (h : RepresentsRelSubPic M.toBase s (algEquivZeroCut M.toBase s) D) :
    SmoothOfRelativeDimension (genusFF K F) D.toBase := by sorry
