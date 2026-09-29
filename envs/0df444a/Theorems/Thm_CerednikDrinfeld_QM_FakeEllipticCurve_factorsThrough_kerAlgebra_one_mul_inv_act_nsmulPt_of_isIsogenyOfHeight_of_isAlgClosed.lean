-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_kerAlgebra_one_mul_inv_act_nsmulPt_of_isIsogenyOfHeight_of_isAlgClosed
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_kerAlgebra_one_mul_inv_act_nsmulPt_of_isIsogenyOfHeight_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/2a7f2232-089f-58e0-aebd-8af2d1d3b414
-- title:
--   Kernel of a formal mathcal O_D-isogeny: subgroup, Λ-stable, r-power torsion
-- statement:
--   Fix rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, a natural number $N$, a prime $r$, and a map $\mathrm{coord}:\Lambda\to \mathbb Z_{p^2}\text{-pairs}$, $\mathrm{coord}:\Lambda\to Z_{p^2}(r)\times Z_{p^2}(r)$ (Witt vectors of $\mathbb F_{r^2}$), satisfying `IsOrderCoord`: additivity, $1\mapsto(1,0)$, the twisted multiplication rule with Frobenius and the factor $r$, injectivity, $r$-adic density of the image, and the trace condition. Let $k$ be an algebraically closed field in which $r$ is nilpotent, let $A$ be a fake elliptic curve over $k$ for $(\Lambda,N)$ — an abelian scheme $A.f:A\to\operatorname{Spec} k$ with relative group law $A.L$, two-dimensional fibres and an action $A.\mathrm{act}$ of $\Lambda$ — let $X_A$ be a formal $\mathcal O_D$-module over $k$ and $\theta_A$ a system of formal coordinates in two variables for $A.f$, with `IsFormalModuleVia`: $\theta_A$ presents $A.L$ along the identity section with formal group law $X_A.F$, and intertwines the action of $m\in\Lambda$ with $X_A.\mathrm{act}(\mathrm{coord}\,m)_1$ added via $X_A.F$ to $X_A.\mathrm{act}(\mathrm{coord}\,m)_2\circ X_A.\varpi$. Let $\gamma$ be a pair of power series which is an $\mathcal O_D$-homomorphism $X_A\to Y$ with kernel of degree $r^h$. Put $R=k[[X_1,X_2]]/(\gamma_1,\gamma_2)$ and let $\iota$ be the underlying morphism $\operatorname{Spec} R\to A$ of the point $\theta_A$ evaluated at the images of $X_1,X_2$. Say a point $P$ of $A$ over $t:T\to\operatorname{Spec} k$ factors through $\iota$ if $P$ is $\iota$ precomposed with some $T\to\operatorname{Spec} R$. Then: the identity $A.L.\mathrm{one}\,t$ factors through $\iota$ for every $t$; if $P,Q$ factor through $\iota$ then so do $A.L.\mathrm{mul}\,t\,P\,Q$ and $A.L.\mathrm{inv}\,t\,P$; if $P$ factors through $\iota$ then so does the push-forward of $P$ along $A.\mathrm{act}\,x$ for every $x\in\Lambda$; and there is a $c\in\mathbb N$, independent of $T$, $t$ and $P$, such that every $P$ factoring through $\iota$ satisfies $r^c\cdot P=A.L.\mathrm{one}\,t$, the $r^c$-fold multiple being the iterated group law.
--
--   This is the group-theoretic content of the statement that the kernel of a formal $\mathcal O_D$-isogeny out of a fake elliptic curve is a finite flat subgroup scheme stable under the quaternionic action and annihilated by a power of $r$: it records that the locus cut out by $\gamma$ contains the identity, is closed under multiplication, inversion and the $\Lambda$-action, and is $r^c$-torsion. It feeds the assembly of the kernel as a closed subgroup, used in the Čerednik–Drinfeld uniformisation of the relevant Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_kerAlgebra_one_mul_inv_act_nsmulPt_of_isIsogenyOfHeight_of_isAlgClosed.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_kerAlgebra_one_mul_inv_act_nsmulPt_of_isIsogenyOfHeight_of_isAlgClosed
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {r : ℕ} [Fact r.Prime]
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (k : Type) [Field k] [IsAlgClosed k] (hkr : IsNilpotent ((r : ℕ) : k))
    (A : FakeEllipticCurve Λ N k) (XA : FormalODModule r k) (θA : RelativeGroupLaw.FormalCoordinates A.f 2)
    (hA : A.IsFormalModuleVia coord XA θA)
    (Y : FormalODModule r k) (γ : Series k) (h : ℕ) (hγ : FormalODModule.IsIsogenyOfHeight XA Y γ h) :
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough (θA (FormalODModule.KerAlgebra γ) (fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i))).1 (A.L.one t)) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t A.f),
      FactorsThrough (θA (FormalODModule.KerAlgebra γ) (fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i))).1 P → FactorsThrough (θA (FormalODModule.KerAlgebra γ) (fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i))).1 Q →
        FactorsThrough (θA (FormalODModule.KerAlgebra γ) (fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i))).1 (A.L.mul t P Q) ∧ FactorsThrough (θA (FormalODModule.KerAlgebra γ) (fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i))).1 (A.L.inv t P)) ∧
    (∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A.f),
      FactorsThrough (θA (FormalODModule.KerAlgebra γ) (fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i))).1 P → FactorsThrough (θA (FormalODModule.KerAlgebra γ) (fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i))).1 (pushPt (A.act x) (A.act_over x) P)) ∧
    (∃ c : ℕ, ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A.f),
      FactorsThrough (θA (FormalODModule.KerAlgebra γ) (fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i))).1 P → nsmulPt A.L t (r ^ c) P = A.L.one t) := by sorry
