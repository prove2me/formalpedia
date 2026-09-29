-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFormalCoordinates_quotient_comp_eq_nilEval_of_factorsThrough_iff_nilEval_eq_zero_of_isAlgClosed
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFormalCoordinates_quotient_comp_eq_nilEval_of_factorsThrough_iff_nilEval_eq_zero_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/f25ad8e1-511c-5bc5-bf61-ed3b65d482a5
-- title:
--   Formal module of the quotient by a formal isogeny kernel
-- statement:
--   Fix rationals $a,b$, an $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$ containing $1$ and all rational integers, a natural number $N$, a prime $r$, and a coordinate map $\mathrm{coord}:\Lambda\to \mathbb{Z}_{r^2}\times\mathbb{Z}_{r^2}$ satisfying `IsOrderCoord` (additive, sending $1$ to $(1,0)$, multiplicative in the twisted sense involving $r$ and the Witt-vector Frobenius, injective, with dense image and the prescribed trace identity). Let $k$ be an algebraically closed field in which $r$ is nilpotent, let $A$ be a `FakeEllipticCurve` for $(\Lambda,N)$ over $k$ (a scheme $A.A\to\operatorname{Spec}k$ with commutative relative group law $A.L$, the abelian-scheme property bundle, two-dimensional fibres and a $\Lambda$-action `A.act`), and let $\theta_A$ be two-dimensional formal coordinates making $A$ a formal $\mathcal{O}_D$-module via $\mathrm{coord}$ with formal module $X_A$ of height $4$. Let $\gamma$ be an isogeny of formal $\mathcal{O}_D$-modules $X_A\to Y$ of height $h$, i.e. an $\mathcal{O}_D$-homomorphism whose kernel algebra has degree $r^h$. Let $\iota:K\to A.A$ be a closed immersion with $\iota$ followed by $A.f$ finite, flat and locally of finite presentation of fibre rank $r^h$ everywhere, such that the points of $A$ factoring through $\iota$ contain each unit section, are closed under $A.L$-multiplication and inversion, are stable under every `A.act x`, are killed by $r^c$ for a fixed $c$, and, for every $k$-algebra $B''$ with an ideal $J$ satisfying $J^{n+1}=\bot$ and every $s:\mathrm{Fin}\,2\to J$, satisfy: $\theta_A(s)$ factors through $\iota$ exactly when all nilpotent evaluations $\mathrm{nilEval}\,n\,(\gamma_i)\,s$ vanish. Let $f':A'\to\operatorname{Spec}k$ carry a commutative relative group law $L'$, the abelian-scheme property bundle, two-dimensional fibres and maps `act' x` over $f'$ that are $L'$-homomorphisms, and let $p:A.A\to A'$, $\psi:A'\to A.A$ be morphisms over $\operatorname{Spec}k$ such that $p$ is a group homomorphism intertwining `A.act` and `act'`, is finite, flat, locally of finite presentation and surjective, has kernel exactly the points factoring through $\iota$, $\psi$ is a group homomorphism intertwining `act'` and `A.act`, $\psi\circ p$ and $p\circ\psi$ induce multiplication by $r^c$ on points, and $p$ has the universal property of the quotient: every homomorphism $\varphi$ from $A$ to a group law $L_X$ over $k$ killing the points factoring through $\iota$ factors uniquely through $p$ by a homomorphism. Then there exist two-dimensional formal coordinates $\theta'$ for $f'$ such that $\theta'$ are formal coordinates for $L'$ with formal group law $Y.F$; for every $k$-algebra $B'$, ideal $J$ with $J^{m+1}=\bot$, $x\in\Lambda$ and $s$ with values in $J$, $\theta'$ applied to the nilpotent evaluation of $\mathrm{addVia}\,Y.F\,(Y.\mathrm{act}(\mathrm{coord}\,x)_1)\,((Y.\mathrm{act}(\mathrm{coord}\,x)_2)\circ Y.\varpi)$ at $s$ equals the pushforward of $\theta'(s)$ along `act' x`; and, for all such $B''$, $J$, $m$, $s$, the point $\theta_A(s)$ followed by $p$ equals $\theta'$ evaluated at the nilpotent evaluations of $\gamma$ at $s$.
--
--   This is the statement that the quotient of a fake elliptic curve by a finite flat $\Lambda$-stable subgroup scheme cut out infinitesimally by a formal $\mathcal{O}_D$-isogeny $\gamma:X_A\to Y$ has $Y$ as its formal $\mathcal{O}_D$-module, with the formal germ of the quotient map equal to $\gamma$ and the $\Lambda$-action on the quotient matching the $\mathcal{O}_D$-action of $Y$ through $\mathrm{coord}$. It feeds the construction of rigidified curves and the transport of formal structure in the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFormalCoordinates_quotient_comp_eq_nilEval_of_factorsThrough_iff_nilEval_eq_zero_of_isAlgClosed.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFormalCoordinates_quotient_comp_eq_nilEval_of_factorsThrough_iff_nilEval_eq_zero_of_isAlgClosed
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {r : ℕ} [Fact r.Prime]
    (hΛ1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (k : Type) [Field k] [IsAlgClosed k] (hkr : IsNilpotent ((r : ℕ) : k))

    (A : FakeEllipticCurve Λ N k) (XA : FormalODModule r k) (θA : RelativeGroupLaw.FormalCoordinates A.f 2)
    (hA : A.IsFormalModuleVia coord XA θA) (hA4 : XA.HasHeight 4)

    (Y : FormalODModule r k) (γ : Series k) (h : ℕ) (hγ : FormalODModule.IsIsogenyOfHeight XA Y γ h)

    (K : Scheme.{0}) (ι : K ⟶ A.A) (hι_closed : IsClosedImmersion ι)
    (hι_finite : IsFinite (ι ≫ A.f)) (hι_flat : Flat (ι ≫ A.f)) (hι_fp : LocallyOfFinitePresentation (ι ≫ A.f))
    (hι_rank : ∀ y : ↥(Spec (CommRingCat.of k)), (ι ≫ A.f).finrank y = r ^ h)
    (hK_one : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough ι (A.L.one t))
    (hK_sub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t A.f),
      FactorsThrough ι P → FactorsThrough ι Q → FactorsThrough ι (A.L.mul t P Q) ∧ FactorsThrough ι (A.L.inv t P))
    (hK_stable : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A.f),
      FactorsThrough ι P → FactorsThrough ι (pushPt (A.act x) (A.act_over x) P))
    (c : ℕ)
    (hK_torsion : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A.f),
      FactorsThrough ι P → nsmulPt A.L t (r ^ c) P = A.L.one t)
    (hKγ : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
        (FactorsThrough ι (θA B'' s) ↔ ∀ i, MvFormalGroup.nilEval n (γ i) s = 0))

    (A' : Scheme.{0}) (f' : A' ⟶ Spec (CommRingCat.of k)) (L' : RelativeGroupLaw k f') (act' : ↥Λ → (A' ⟶ A'))
    (hact' : ∀ x : ↥Λ, act' x ≫ f' = f')
    (p : A.A ⟶ A') (hp : p ≫ f' = A.f) (ψ : A' ⟶ A.A) (hψ : ψ ≫ A.f = f')
    (hL'_comm : L'.IsCommutative)
    (hA'_bundle : AbelianSchemePropertyBundle k f')
    (hA'_dim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f'.base ⁻¹' {s}) = 2)
    (hact'_mul : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f'),
      pushPt (act' x) (hact' x) (L'.mul t P Q) = L'.mul t (pushPt (act' x) (hact' x) P) (pushPt (act' x) (hact' x) Q))

    (hp_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t A.f),
      mapPt p hp (A.L.mul t P Q) = L'.mul t (mapPt p hp P) (mapPt p hp Q))
    (hp_act : ∀ x : ↥Λ, A.act x ≫ p = p ≫ act' x)
    (hp_finite : IsFinite p) (hp_flat : Flat p) (hp_fp : LocallyOfFinitePresentation p) (hp_surj : Surjective p)
    (hp_ker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A.f),
      mapPt p hp P = L'.one t ↔ FactorsThrough ι P)

    (hψ_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f'),
      mapPt ψ hψ (L'.mul t P Q) = A.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    (hψ_act : ∀ x : ↥Λ, act' x ≫ ψ = ψ ≫ A.act x)
    (hψp : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A.f),
      mapPt ψ hψ (mapPt p hp P) = nsmulPt A.L t (r ^ c) P)
    (hpψ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t f'),
      mapPt p hp (mapPt ψ hψ Q) = nsmulPt L' t (r ^ c) Q)

    (hp_univ : ∀ (X : Scheme.{0}) (gX : X ⟶ Spec (CommRingCat.of k)) (LX : RelativeGroupLaw k gX) (φ : A.A ⟶ X) (hφ : φ ≫ gX = A.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t A.f),
        mapPt φ hφ (A.L.mul t P Q) = LX.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A.f),
        FactorsThrough ι P → mapPt φ hφ P = LX.one t) →
      ∃! χ : SchemeHomOver f' gX, p ≫ χ.1 = φ ∧
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (u v : SchemeHomOver t f'),
          mapPt χ.1 χ.2 (L'.mul t u v) = LX.mul t (mapPt χ.1 χ.2 u) (mapPt χ.1 χ.2 v)) :
    ∃ θ' : RelativeGroupLaw.FormalCoordinates f' 2,

      L'.IsFormalCoordinates Y.F θ' ∧
      (∀ (B' : Type) [CommRing B'] [Algebra k B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
        ∀ (x : ↥Λ) (s : Fin 2 → B'), (∀ i, s i ∈ J) →
          θ' B' (fun i => MvFormalGroup.nilEval m
              (Series.addVia Y.F (Y.act (coord x).1) ((Y.act (coord x).2).comp Y.varpi) i) s) =
            pushPt (act' x) (hact' x) (θ' B' s)) ∧

      (∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          (θA B'' s).1 ≫ p = (θ' B'' (fun i => MvFormalGroup.nilEval m (γ i) s)).1) := by sorry
