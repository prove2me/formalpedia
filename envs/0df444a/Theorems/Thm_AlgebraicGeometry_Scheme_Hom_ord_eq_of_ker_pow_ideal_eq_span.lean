-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_ord_eq_of_ker_pow_ideal_eq_span
-- name    : AlgebraicGeometry.Scheme.Hom.ord_eq_of_ker_pow_ideal_eq_span
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/d4a9bf47-1b3a-56bf-bb43-bff814b81dbb
-- title:
--   Order of a generator of mathcal I_P^{ n} at centred places
-- statement:
--   Let $K$ be a field, $X$ an integral scheme with a morphism $x \colon X \to \operatorname{Spec} K$ that is separated, and let $P \colon \operatorname{Spec} K \to X$ be a section of $x$, i.e. $P$ followed by $x$ is the identity of $\operatorname{Spec} K$. Fix $n \in \mathbb{N}$, an open $U \subseteq X$ together with a proof that $U$ is affine, and $g \in \Gamma(X, U)$ such that the ideal cut out on $U$ by the $n$-th power of the kernel ideal sheaf of $P$ equals the ideal $(g)$ of $\Gamma(X,U)$. Fix further a point $y \in U$ whose singleton is closed in $X$, and an element $v$ of $\mathrm{AlgebraicCurve.Place}\ K\ X.\mathrm{functionField}$, that is, a valuation subring of the function field of $X$ which contains the image of $K$ under the ring map $K \to X.\mathrm{functionField}$ obtained from $x$ by taking global sections and then the germ at the generic point, is not the whole field, and is a principal ideal ring; assume $v$ is centred at $y$, in the sense that its underlying subring is exactly the image of the stalk $\mathcal O_{X,y}$ in $X.\mathrm{functionField}$. The conclusion is the conjunction of two implications for the image of $g$ in $X.\mathrm{functionField}$: if the image of the closed point of $\operatorname{Spec} K$ under $P$ is $y$, then $\operatorname{ord}_v(g) = n$, and if it is not $y$, then $\operatorname{ord}_v(g) = 0$. Here $\operatorname{ord}_v$ denotes minus the logarithm of the valuation attached to the height-one prime of the valuation subring of $v$.
--
--   This is the local computation identifying the Weil divisor attached to the effective divisor $n \cdot P$ at a rational point $P$ of a curve with $n$ times the place centred at $P$: a local generator of $\mathcal I_P^{\,n}$ has order $n$ at the place of $P$ and order $0$ at every other place centred at a closed point of the chosen affine open. It is used in the passage from invertible ideal sheaves and their local generators to divisor classes, and enters the construction of the relative Picard group data and the principality statements for presentations of $\mathcal I_P^{\,n}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_ord_eq_of_ker_pow_ideal_eq_span.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.ord_eq_of_ker_pow_ideal_eq_span
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsSeparated x]
    (P : Spec (CommRingCat.of K) ⟶ X) (hP : P ≫ x = 𝟙 _) (n : ℕ)
    (U : X.Opens) (hU : IsAffineOpen U) (g : Γ(X, U)) (hg : (P.ker ^ n).ideal ⟨U, hU⟩ = Ideal.span {g})
    (y : X) (hyU : y ∈ U) (hy : IsClosed ({y} : Set X))
    (v : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Place K X.functionField)
    (hv : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
    (P.base (IsLocalRing.closedPoint K) = y → v.ord (algebraMap Γ(X, U) X.functionField g) = n) ∧
      (P.base (IsLocalRing.closedPoint K) ≠ y → v.ord (algebraMap Γ(X, U) X.functionField g) = 0) := by sorry
