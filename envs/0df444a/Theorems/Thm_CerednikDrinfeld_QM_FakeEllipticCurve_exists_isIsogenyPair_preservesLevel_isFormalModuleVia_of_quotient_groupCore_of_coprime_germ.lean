-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isIsogenyPair_preservesLevel_isFormalModuleVia_of_quotient_groupCore_of_coprime_germ
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isIsogenyPair_preservesLevel_isFormalModuleVia_of_quotient_groupCore_of_coprime_germ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/82791c8c-f589-595c-ada5-e84b373eb763
-- title:
--   Quotient by a finite Λ-stable n-torsion subgroup is again fake elliptic
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$ which is an order (contains $1$, is multiplicatively closed, spans over $\mathbb{Q}$ and is finitely generated), a level $N$, a prime $r$, a map $\mathrm{coord}:\Lambda\to \mathrm{Zp2}\,r\times \mathrm{Zp2}\,r$, an algebraically closed field $k$, a fake elliptic curve $E_0$ of level $N$ for $\Lambda$ over $k$, a formal $\mathcal{O}_D$-module $X_0$ over $k$ for $r$, a system $\theta_0$ of $2$-dimensional formal coordinates along the unit section of $E_0.f$, and $n$ with $\gcd(n,N)=1$. Assume given $\iota:K_0\to E_0.A$ such that every point of $E_0$ factoring through $\iota$ is killed by $n$; a scheme $A$ over $\operatorname{Spec}k$ with a commutative relative group law $L$, the abelian-scheme property bundle (smooth, proper, connected fibres, a group law exists), all fibres of topological Krull dimension $2$, and a $\Lambda$-action `act` over the base which is additive, multiplicative, unital and additive in $\Lambda$; morphisms $p:E_0.A\to A$ and $\psi:A\to E_0.A$ over $k$, both group-law homomorphisms, $\Lambda$-equivariant, with $p$ finite, with $p$ having kernel exactly the points factoring through $\iota$, and with $\psi\circ p=[n]$ on $E_0$ and $p\circ\psi=[n]$ on $A$; Drinfeld's trace condition for $(A,L,\mathrm{act})$, stating that for any algebraically closed $k'$ receiving $k$ and any finite-dimensional $k'$-space $V$ parametrising the tangent vectors at the unit compatibly with addition and scaling, the trace of the endomorphism induced by $m\in\Lambda$ equals the reduced trace $m+\bar m$; and $2$-dimensional formal coordinates $\theta$ for $L$ with formal group $X.F$, equivariant for $\Lambda$ through $\mathrm{coord}$ in the sense that the substitution $\mathrm{addVia}\,X.F\,(X.\mathrm{act}(\mathrm{coord}\,x)_1)\,((X.\mathrm{act}(\mathrm{coord}\,x)_2)\circ X.\varpi)$ computes the action of `act x`, together with an $\mathcal{O}_D$-homomorphism $\gamma_p:X_0\to X$ through which $p$ acts on nilpotent formal points, i.e. $\theta_0(s)$ followed by $p$ equals $\theta$ evaluated at the truncated substitution of $s$ into $\gamma_p$. Then there exist a fake elliptic curve $E$ of level $N$ for $\Lambda$ over $k$, morphisms $q:E_0.A\to E.A$ and $q':E.A\to E_0.A$ over $\operatorname{Spec}k$, and formal coordinates $\theta_E$ for $E.f$, such that $(q,q')$ is an $n$-isogeny pair (both are group-law homomorphisms, both commute with the $\Lambda$-actions, and $q\circ q'$, $q'\circ q$ are the action of $n$ whenever $n\in\Lambda$), both $q$ and $q'$ preserve the level structures, the points of $E_0$ killed by $q$ are exactly those factoring through $\iota$, $E$ is a formal module via $\mathrm{coord}$, $X$ and $\theta_E$, and $\theta_0(s)$ followed by $q$ equals $\theta_E$ at the truncated substitution of $s$ into $\gamma_p$.
--
--   This is the packaging step of the quotient construction for fake elliptic curves: from a group-scheme quotient of $E_0$ by a finite $\Lambda$-stable subgroup annihilated by $n$ prime to $N$ it produces the quotient again as an object of the moduli problem, $n$-isogenous to $E_0$ by a level-preserving isogeny and carrying the prescribed formal $\mathcal{O}_D$-module structure and germ. It feeds the construction of rigidified curves with prescribed rigid transport used in the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isIsogenyPair_preservesLevel_isFormalModuleVia_of_quotient_groupCore_of_coprime_germ.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isIsogenyPair_preservesLevel_isFormalModuleVia_of_quotient_groupCore_of_coprime_germ
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {r : ℕ} [Fact r.Prime]
    (coord : ↥Λ → Zp2 r × Zp2 r)
    (k : Type) [Field k] [IsAlgClosed k] (E₀ : FakeEllipticCurve Λ N k) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (X₀ : FormalODModule r k) (θ₀ : RelativeGroupLaw.FormalCoordinates E₀.f 2)
    (n : ℕ) (hnN : Nat.Coprime n N)

    (K₀ : Scheme.{0}) (ι : K₀ ⟶ E₀.A)
    (hK_torsion : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
      FactorsThrough ι P → nsmulPt E₀.L t n P = E₀.L.one t)

    (A : Scheme.{0}) (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) (act : ↥Λ → (A ⟶ A))
    (hact : ∀ x : ↥Λ, act x ≫ f = f)
    (p : E₀.A ⟶ A) (hp : p ≫ f = E₀.f) (ψ : A ⟶ E₀.A) (hψ : ψ ≫ E₀.f = f)
    (hcomm : L.IsCommutative)
    (hbundle : AbelianSchemePropertyBundle k f)
    (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = 2)
    (hact_hom : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      pushPt (act x) (hact x) (L.mul t P Q) = L.mul t (pushPt (act x) (hact x) P) (pushPt (act x) (hact x) Q))
    (hact_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 A)
    (hact_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x)
    (hact_add : ∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f),
      pushPt (act (x + y)) (hact (x + y)) P = L.mul t (pushPt (act x) (hact x) P) (pushPt (act y) (hact y) P))
    (hp_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E₀.f),
      mapPt p hp (E₀.L.mul t P Q) = L.mul t (mapPt p hp P) (mapPt p hp Q))
    (hequiv : ∀ x : ↥Λ, E₀.act x ≫ p = p ≫ act x)
    (hp_finite : IsFinite p)
    (hker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
      mapPt p hp P = L.one t ↔ FactorsThrough ι P)
    (hψ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      mapPt ψ hψ (L.mul t P Q) = E₀.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    (hψ_lin : ∀ x : ↥Λ, act x ≫ ψ = ψ ≫ E₀.act x)
    (hψp : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
      mapPt ψ hψ (mapPt p hp P) = nsmulPt E₀.L t n P)
    (hpψ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t f),
      mapPt p hp (mapPt ψ hψ Q) = nsmulPt L t n Q)

    (htrace : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k')
      (V : Type) [AddCommGroup V] [Module k' V] [Module.Finite k' V] (τ : V → SchemeHomOver (tangentBase k' sk) f),
      Function.Injective τ →
      (∀ P : SchemeHomOver (tangentBase k' sk) f, P ∈ Set.range τ ↔ IsTangentVector L k' sk P) →
      (∀ v w : V, τ (v + w) = L.mul (tangentBase k' sk) (τ v) (τ w)) →
      (∀ (c : k') (v : V), (τ (c • v)).1 = tangentScale k' c ≫ (τ v).1) →
      ∀ (m : ↥Λ) (Φ : V →ₗ[k'] V), (∀ v : V, τ (Φ v) = pushPt (act m) (hact m) (τ v)) →
      ∀ n' : ℤ, (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n' : ℚ) : ℍ[ℚ, a, b]) →
        LinearMap.trace k' V Φ = (n' : k'))

    (X : FormalODModule r k) (θ : RelativeGroupLaw.FormalCoordinates f 2) (hθ : L.IsFormalCoordinates X.F θ)
    (hθact : ∀ (B' : Type) [CommRing B'] [Algebra k B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
      ∀ (x : ↥Λ) (s : Fin 2 → B'), (∀ i, s i ∈ J) →
        θ B' (fun i => MvFormalGroup.nilEval m
            (Series.addVia X.F (X.act (coord x).1) ((X.act (coord x).2).comp X.varpi) i) s) =
          pushPt (act x) (hact x) (θ B' s))
    (γp : Series k) (hγp : FormalODModule.IsODHom X₀ X γp)
    (hgerm : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ →
      ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
        (θ₀ B'' s).1 ≫ p = (θ B'' (fun i => MvFormalGroup.nilEval m (γp i) s)).1) :
    ∃ (E : FakeEllipticCurve Λ N k) (q : E₀.A ⟶ E.A) (hq : q ≫ E.f = E₀.f) (q' : E.A ⟶ E₀.A) (hq' : q' ≫ E₀.f = E.f)
      (θE : RelativeGroupLaw.FormalCoordinates E.f 2),
      FakeEllipticCurve.IsIsogenyPair n E₀ E q q' ∧
      FakeEllipticCurve.PreservesLevel E₀ E q hq ∧ FakeEllipticCurve.PreservesLevel E E₀ q' hq' ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        mapPt q hq P = E.L.one t ↔ FactorsThrough ι P) ∧
      E.IsFormalModuleVia coord X θE ∧
      (∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          (θ₀ B'' s).1 ≫ q = (θE B'' (fun i => MvFormalGroup.nilEval m (γp i) s)).1) := by sorry
