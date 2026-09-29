-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isClosedImmersion_formalCoordinates_kerAlgebra_of_isIsogenyOfHeight_of_isAlgClosed
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isClosedImmersion_formalCoordinates_kerAlgebra_of_isIsogenyOfHeight_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/d5b241bc-a2d3-5515-96f4-6a302755b0db
-- title:
--   Formal isogeny kernel embeds as finite flat closed subscheme
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$ and a prime $r$, and let $\mathrm{coord}:\Lambda\to \mathbb{Z}_{r^2}\times\mathbb{Z}_{r^2}$ (Witt vectors over the field with $r^2$ elements) satisfy `IsOrderCoord`: it is additive, sends $1$ to $(1,0)$, is injective, satisfies the twisted multiplication rule $\mathrm{coord}(mm')=(x x'+r\,y\,\sigma(y'),\,x y'+y\,\sigma(x'))$ with $\sigma$ the Witt-vector Frobenius, has dense image modulo every power of $r$, and matches reduced traces with $x+\sigma(x)$. Let $k$ be an algebraically closed field in which the image of $r$ is nilpotent, $A$ a fake elliptic curve over $k$ for $(\Lambda,N)$ with structure morphism $A.f$ to $\operatorname{Spec} k$ and relative commutative group law $A.L$, $X_A$ a formal $\mathcal{O}_D$-module over $k$ of dimension $2$ (a commutative formal group law with a $\mathbb{Z}_{r^2}$-action and a uniformiser series $\varpi$ with $\varpi\circ\varpi=[r]$ and $\varpi\circ[\alpha]=[\sigma\alpha]\circ\varpi$), and $\theta_A$ a system of formal coordinates of dimension $2$ for $A.f$; assume `IsFormalModuleVia`, i.e. $\theta_A$ are formal coordinates for $A.L$ with formal group $X_A.F$ and translate the $\Lambda$-action on $A$ into the $\mathrm{coord}$-twisted action of $X_A$. Let $Y$ be a second formal $\mathcal{O}_D$-module, $\gamma=(\gamma_0,\gamma_1)$ a pair of power series in two variables over $k$ which is an $\mathcal{O}_D$-homomorphism $X_A\to Y$ whose kernel has degree $r^h$. Put $R:=k[[X_0,X_1]]/(\gamma_0,\gamma_1)$ and let $\iota:\operatorname{Spec} R\to A$ be the scheme morphism underlying the $R$-point $\theta_A(R)$ evaluated at the classes of $X_0,X_1$. Then $\iota$ is a closed immersion, and $\iota$ followed by $A.f$ is finite, flat and locally of finite presentation, with fibre rank $r^h$ at every point of $\operatorname{Spec} k$.
--
--   This realises the scheme-theoretic kernel of an $\mathcal{O}_D$-isogeny of height $h$ of the formal module of a fake elliptic curve as a closed subscheme of $A$ which is finite flat of rank $r^h$ over the base; the group-law properties of this subscheme and the description of its points are treated separately. It is used in the characterisation of the closed subgroups of $A$ through which a given point factors in terms of the vanishing of truncated evaluations of $\gamma$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isClosedImmersion_formalCoordinates_kerAlgebra_of_isIsogenyOfHeight_of_isAlgClosed.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isClosedImmersion_formalCoordinates_kerAlgebra_of_isIsogenyOfHeight_of_isAlgClosed
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {r : ℕ} [Fact r.Prime]
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (k : Type) [Field k] [IsAlgClosed k] (hkr : IsNilpotent ((r : ℕ) : k))
    (A : FakeEllipticCurve Λ N k) (XA : FormalODModule r k) (θA : RelativeGroupLaw.FormalCoordinates A.f 2)
    (hA : A.IsFormalModuleVia coord XA θA)
    (Y : FormalODModule r k) (γ : Series k) (h : ℕ) (hγ : FormalODModule.IsIsogenyOfHeight XA Y γ h) :
    IsClosedImmersion (θA (FormalODModule.KerAlgebra γ) (fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i))).1 ∧
      IsFinite ((θA (FormalODModule.KerAlgebra γ) (fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i))).1 ≫ A.f) ∧
      Flat ((θA (FormalODModule.KerAlgebra γ) (fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i))).1 ≫ A.f) ∧
      LocallyOfFinitePresentation ((θA (FormalODModule.KerAlgebra γ) (fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i))).1 ≫ A.f) ∧
      (∀ y : ↥(Spec (CommRingCat.of k)),
        ((θA (FormalODModule.KerAlgebra γ) (fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i))).1 ≫ A.f).finrank y = r ^ h) := by sorry
