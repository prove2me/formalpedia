-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_isRational_of_range_stalk_section_eq
-- name    : AlgebraicCurve.Place.isRational_of_range_stalk_section_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/3651dc49-034c-51a3-81d7-692939622b47
-- title:
--   Rationality of the place at a k-point of an integral scheme
-- statement:
--   Let $k$ be a field and let $X$ be an integral scheme equipped with a morphism $c \colon X \to \operatorname{Spec} k$, and let $\sigma \colon \operatorname{Spec} k \to X$ be a section of $c$, i.e. $\sigma$ followed by $c$ is the identity of $\operatorname{Spec} k$. The function field $k(X) =$ `X.functionField` is regarded as a $k$-algebra through [`AlgebraicCurve.baseToFunctionField c`](def/AlgebraicCurve_CurveModel.html#L18), the ring map sending $a \in k$ to the germ at the generic point of $X$ of the global section $c^{\sharp}(a)$ (the image of $a$ under the inverse of the $\Gamma$–$\operatorname{Spec}$ adjunction isomorphism, pushed forward by $c$ on global sections). Let $v$ be a place of $k(X)$ over $k$ in the sense of this development: a valuation subring $\mathcal O_v \subseteq k(X)$ containing the image of $k$, different from all of $k(X)$, and which is a principal ideal ring. Assume that the range of the algebra map from the stalk $\mathcal O_{X,\sigma(\mathrm{pt})}$ at the image of the closed point of $\operatorname{Spec} k$ into $k(X)$ is, as a subring, exactly $\mathcal O_v$. Then $v$ is rational, meaning that the induced map from $k$ to the residue field $\mathcal O_v / \mathfrak m_v$ is surjective.
--
--   This is the statement that a place of the function field whose valuation ring is the local ring at a $k$-rational point of an integral $k$-scheme has residue field $k$, i.e. is a rational place. It is used when matching places of the function field with points of a curve model, and in the analysis of Serre-type pairings over a perfect base field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_isRational_of_range_stalk_section_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem AlgebraicCurve.Place.isRational_of_range_stalk_section_eq
    {k : Type u} [Field k] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X]
    (σ : Spec (CommRingCat.of k) ⟶ X) (hσ : σ ≫ c = 𝟙 _) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∀ (v : AlgebraicCurve.Place k X.functionField),
      (algebraMap (X.presheaf.stalk (σ.base (IsLocalRing.closedPoint k))) X.functionField).range =
        v.toValuationSubring.toSubring → v.IsRational := by sorry
