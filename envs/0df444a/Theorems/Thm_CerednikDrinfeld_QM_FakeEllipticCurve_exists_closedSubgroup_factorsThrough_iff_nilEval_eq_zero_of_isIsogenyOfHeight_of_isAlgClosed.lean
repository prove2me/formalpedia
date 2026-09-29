-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_closedSubgroup_factorsThrough_iff_nilEval_eq_zero_of_isIsogenyOfHeight_of_isAlgClosed
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_closedSubgroup_factorsThrough_iff_nilEval_eq_zero_of_isIsogenyOfHeight_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/e3e02691-e399-5004-9e07-8a2ce08e956d
-- title:
--   Kernel subgroup scheme of a formal mathcal O_D-isogeny
-- statement:
--   Fix rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, a natural number $N$ and a prime $r$. Let $\mathrm{coord}:\Lambda\to W(\mathbb F_{r^2})^2$ be an order coordinatisation, i.e. additive, injective, sending $1$ (when $1\in\Lambda$) to $(1,0)$, multiplicative for the twisted rule $\mathrm{coord}(mm')=(c_1c_1'+r\,c_2\,\varphi(c_2'),\,c_1c_2'+c_2\,\varphi(c_1'))$ with $\varphi$ the Witt-vector Frobenius, with dense image modulo every power of $r$ and with $c_1+\varphi(c_1)=n$ whenever $m+\bar m=n$. Let $k$ be an algebraically closed field in which $r$ is nilpotent, $A$ a fake elliptic curve of level data $(\Lambda,N)$ over $k$ (a scheme `A.A` with structure morphism `A.f` to $\operatorname{Spec} k$, a commutative relative group law `A.L`, the abelian-scheme property bundle, two-dimensional fibres, and an action `A.act` of $\Lambda$ over $\operatorname{Spec} k$), $XA$ a formal $\mathcal O_D$-module over $k$ (a commutative two-dimensional formal group with $W(\mathbb F_{r^2})$-action and uniformiser series), and $\theta A$ a system of formal coordinates in two variables for `A.f`, assigning to each $k$-algebra $B'$ and each $s:\mathrm{Fin}\,2\to B'$ a point of $A$ over $\operatorname{Spec} B'$, assumed to be a formal-module coordinatisation via $\mathrm{coord}$: $\theta A$ parametrises `A.L` by $XA.F$ and carries the $XA$-action of $\mathrm{coord}(m)$ to the action of $m$ on nilpotent points. Let $Y$ be a further formal $\mathcal O_D$-module, and $\gamma$ a pair of power series in two variables which is an $\mathcal O_D$-homomorphism $XA\to Y$ with kernel of degree $r^h$. Then there exist a scheme $K$ and a morphism $\iota:K\to A$ such that: $\iota$ is a closed immersion; $\iota$ followed by `A.f` is finite, flat and locally of finite presentation, with fibre rank $r^h$ at every point of $\operatorname{Spec} k$; the points of $A$ factoring through $\iota$ contain the identity section, are closed under the group law and inversion, and are stable under $\mathrm{pushPt}$ along `A.act x` for every $x\in\Lambda$; there is $c$ with $r^c$-fold multiplication killing every point factoring through $\iota$; and for every $k$-algebra $B''$, ideal $J$ with $J^{n+1}=0$ and $s:\mathrm{Fin}\,2\to B''$ with all $s_i\in J$, the point $\theta A\,B''\,s$ factors through $\iota$ if and only if $\mathrm{nilEval}\,n\,(\gamma_i)\,s=0$ for each $i$, where $\mathrm{nilEval}$ evaluates the truncation of a power series in degrees $\le n$ in each variable at $s$.
--
--   This is the construction of the scheme-theoretic kernel of a formal $\mathcal O_D$-isogeny out of a fake elliptic curve: a finite flat closed subgroup scheme of rank $r^h$, stable under the quaternionic action and killed by a power of $r$, whose infinitesimal points are exactly the zeros of the isogeny. It is used in the Čerednik–Drinfeld uniformisation step, where such kernels provide the level structures transported along rigid-analytic isomorphisms of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_closedSubgroup_factorsThrough_iff_nilEval_eq_zero_of_isIsogenyOfHeight_of_isAlgClosed.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_closedSubgroup_factorsThrough_iff_nilEval_eq_zero_of_isIsogenyOfHeight_of_isAlgClosed
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {r : ℕ} [Fact r.Prime]
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (k : Type) [Field k] [IsAlgClosed k] (hkr : IsNilpotent ((r : ℕ) : k))
    (A : FakeEllipticCurve Λ N k) (XA : FormalODModule r k) (θA : RelativeGroupLaw.FormalCoordinates A.f 2)
    (hA : A.IsFormalModuleVia coord XA θA)
    (Y : FormalODModule r k) (γ : Series k) (h : ℕ) (hγ : FormalODModule.IsIsogenyOfHeight XA Y γ h) :
    ∃ (K : Scheme.{0}) (ι : K ⟶ A.A),
      IsClosedImmersion ι ∧ IsFinite (ι ≫ A.f) ∧ Flat (ι ≫ A.f) ∧ LocallyOfFinitePresentation (ι ≫ A.f) ∧
      (∀ y : ↥(Spec (CommRingCat.of k)), (ι ≫ A.f).finrank y = r ^ h) ∧

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough ι (A.L.one t)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t A.f),
        FactorsThrough ι P → FactorsThrough ι Q → FactorsThrough ι (A.L.mul t P Q) ∧ FactorsThrough ι (A.L.inv t P)) ∧
      (∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A.f),
        FactorsThrough ι P → FactorsThrough ι (pushPt (A.act x) (A.act_over x) P)) ∧

      (∃ c : ℕ, ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A.f),
        FactorsThrough ι P → nsmulPt A.L t (r ^ c) P = A.L.one t) ∧

      (∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          (FactorsThrough ι (θA B'' s) ↔ ∀ i, MvFormalGroup.nilEval n (γ i) s = 0)) := by sorry
