-- Prove2me | Theorems.Thm_AlgebraicGeometry_SplitTorus_forall_torusPt_mul_of_torusPtId_mul_of_isAlgClosed
-- name    : AlgebraicGeometry.SplitTorus.forall_torusPt_mul_of_torusPtId_mul_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/76b519fd-36c3-5307-99e3-720802d3f757
-- title:
--   Homomorphy on κ-points extends to all points of a split torus
-- statement:
--   Let $\kappa$ be an algebraically closed field, let $Y$ be a scheme and let $f : Y \to \operatorname{Spec}\kappa$ be a separated morphism, and let $L$ be a relative group law for $f$, i.e. a family of binary operations, units and inversions on the sets $\operatorname{SchemeHomOver}(t, f) = \{\varphi : T \to Y \mid \varphi \circ f = t\}$ of relative points, for all $t : T \to \operatorname{Spec}\kappa$, satisfying associativity, the unit laws, left inversion, and naturality under base morphisms $\psi : T' \to T$ over $\operatorname{Spec}\kappa$. Fix $t \in \mathbb{N}$ and let $\tau$ be a relative point of $f$ over the structure morphism $\operatorname{torusStr}\,\kappa\,t$ of the split torus, that is a morphism $\operatorname{Spec}(\kappa[\mathbb{Z}^t]) \to Y$ ($\kappa[\mathbb{Z}^t]$ being the additive monoid algebra on $\mathrm{Fin}\,t \to \mathbb{Z}$) whose composite with $f$ is $\operatorname{Spec}$ of the structure map $\kappa \to \kappa[\mathbb{Z}^t]$. Assume that $\tau$ is multiplicative on $\kappa$-points: for all $\chi, \chi'$ in the type `WithConv` of $\kappa$-algebra maps $\kappa[\mathbb{Z}^t] \to \kappa$ with its multiplication, writing $\operatorname{torusPtId}\kappa\,t\,\chi$ for the $\kappa$-point $\operatorname{Spec}$ of $\chi$ viewed over the identity of $\operatorname{Spec}\kappa$, the composite of $\operatorname{torusPtId}\kappa\,t\,(\chi\chi')$ with $\tau$ equals the $L$-product of the composites of $\operatorname{torusPtId}\kappa\,t\,\chi$ and $\operatorname{torusPtId}\kappa\,t\,\chi'$ with $\tau$. Then the same multiplicativity holds with values in an arbitrary commutative $\kappa$-algebra $T$: for all $\chi, \chi'$ in `WithConv` of the $\kappa$-algebra maps $\kappa[\mathbb{Z}^t] \to T$, the composite of the $T$-point $\operatorname{torusPt}\kappa\,T\,t\,(\chi\chi')$ (a morphism $\operatorname{Spec} T \to \operatorname{Spec}(\kappa[\mathbb{Z}^t])$ over $\operatorname{Spec}$ of $\kappa \to T$) with $\tau$ equals the $L$-product of the composites of $\operatorname{torusPt}\kappa\,T\,t\,\chi$ and $\operatorname{torusPt}\kappa\,T\,t\,\chi'$ with $\tau$.
--
--   This is the passage from homomorphy of a morphism of a split torus into a group object on $\kappa$-valued points to homomorphy on points with values in every commutative $\kappa$-algebra, so that a map recorded as multiplicative on closed points is a homomorphism for the relative group law; it rests on the rigidity statement [`AlgebraicGeometry.SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat`](thm.html#AlgebraicGeometry.SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat), two relative points of a separated target agreeing on all points valued in an algebraic closure being equal. It is used in the construction and uniqueness of lifts of the multiplication on torus fibres over henselian bases, in the recognition of split-torus subgroups by their image, and in the analysis of the special fibre of the group law attached to $X_1(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SplitTorus_forall_torusPt_mul_of_torusPtId_mul_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct AlgebraicGeometry.SplitTorus

theorem AlgebraicGeometry.SplitTorus.forall_torusPt_mul_of_torusPtId_mul_of_isAlgClosed
    {κ : Type u} [Field κ] [IsAlgClosed κ]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of κ)) [IsSeparated f] (L : RelativeGroupLaw κ f) (t : ℕ)
    (τ : SchemeHomOver (torusStr κ t) f)
    (hτmul : ∀ χ χ' : WithConv (torusCoord κ t →ₐ[κ] κ),
      NeronModelInfra.schemeHomOverComp (torusPtId κ t (χ * χ').ofConv) τ =
        L.mul _ (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ.ofConv) τ)
          (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ'.ofConv) τ))
    (T : Type u) [CommRing T] [Algebra κ T] (χ χ' : WithConv (torusCoord κ t →ₐ[κ] T)) :
    NeronModelInfra.schemeHomOverComp (torusPt κ T t (χ * χ').ofConv) τ =
      L.mul _ (NeronModelInfra.schemeHomOverComp (torusPt κ T t χ.ofConv) τ)
        (NeronModelInfra.schemeHomOverComp (torusPt κ T t χ'.ofConv) τ) := by sorry
