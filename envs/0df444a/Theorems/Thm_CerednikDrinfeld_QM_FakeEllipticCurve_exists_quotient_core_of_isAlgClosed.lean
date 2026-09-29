-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_core_of_isAlgClosed
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_quotient_core_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/40a857c3-6fd4-5ba4-b799-c74e88e05ea8
-- title:
--   Quotient of a fake elliptic curve by an n-torsion subgroup
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, and an algebraically closed field $k$; let $E_0$ be a fake elliptic curve of type $(\Lambda,N)$ over $k$, so in particular $E_0.A$ carries a commutative relative group law $E_0.L$ over $E_0.f : E_0.A \to \operatorname{Spec} k$, satisfies the abelian-scheme bundle (smooth, proper, connected fibres, a group law exists), has $2$-dimensional fibres, and is equipped with an action $x \mapsto E_0.\mathrm{act}\,x$ of $\Lambda$ by endomorphisms over $\operatorname{Spec} k$ obeying the unit, multiplicativity, additivity and trace laws. Assume $\Lambda$ is an order (contains $1$, is multiplicatively closed, spans the algebra over $\mathbb{Q}$, finitely generated), and let $n$ be a natural number with $n \neq 0$ in $k$. Let $\iota : K_0 \to E_0.A$ be a closed immersion such that $\iota$ followed by $E_0.f$ is finite, flat and locally of finite presentation, and suppose: for every base $t : T \to \operatorname{Spec} k$ the unit section $E_0.L.\mathrm{one}\,t$ factors through $\iota$; the set of $t$-points factoring through $\iota$ is closed under $E_0.L.\mathrm{mul}$ and $E_0.L.\mathrm{inv}$; it is preserved by each $E_0.\mathrm{act}\,x$, $x \in \Lambda$; and every such point is killed by $n$, i.e. $\mathrm{nsmulPt}\,E_0.L\,t\,n\,P = E_0.L.\mathrm{one}\,t$. The conclusion asserts the existence of a scheme $A$, a morphism $f : A \to \operatorname{Spec} k$, a relative group law $L$ on $f$, maps $\mathrm{act} : \Lambda \to (A \to A)$ over $\operatorname{Spec} k$, and morphisms $p : E_0.A \to A$ over $\operatorname{Spec} k$ and $\psi : A \to E_0.A$ with $\psi$ followed by $E_0.f$ equal to $f$, such that: $L$ is commutative, $f$ satisfies the abelian-scheme property bundle, every fibre of $f$ has topological Krull dimension $2$, and $\mathrm{act}$ satisfies exactly the same four laws as on $E_0$ (each $\mathrm{act}\,x$ is a homomorphism for $L$; $\mathrm{act}\,1 = \mathbb{1}_A$; $\mathrm{act}(xy) = \mathrm{act}\,y$ followed by $\mathrm{act}\,x$; additivity in $x$), together with the trace condition: for every algebraically closed field $k'$, ring map $sk : k \to k'$, finite-dimensional $k'$-space $V$ and injective parametrisation $\tau$ of the tangent vectors of $L$ over the dual-number base which is additive and compatible with scaling, if $\Phi$ is the $k'$-linear endomorphism of $V$ induced by $\mathrm{act}\,m$ and $m + \bar m = n' \in \mathbb{Z}$, then $\operatorname{tr}\Phi = n'$ in $k'$. Moreover $p$ is a homomorphism from $E_0.L$ to $L$, intertwines the two $\Lambda$-actions, is finite, flat, locally of finite presentation, surjective and étale, has at each point $y$ of $A$ the same local rank as $\iota$ followed by $E_0.f$ at $f.\mathrm{base}\,y$, and its kernel is exactly $K_0$: a point $P$ has $\mathrm{mapPt}\,p\,P = L.\mathrm{one}\,t$ if and only if $P$ factors through $\iota$. Likewise $\psi$ is a homomorphism intertwining the actions, with $\psi \circ p = [n]$ on $E_0$ and $p \circ \psi = [n]$ on $A$ (pointwise in the $\mathrm{mapPt}$/$\mathrm{nsmulPt}$ formulation). Finally the universal property holds: for every scheme $X$ over $\operatorname{Spec} k$ with a relative group law $L_X$ and every homomorphism $\varphi : E_0.A \to X$ over $\operatorname{Spec} k$ whose value on points factoring through $\iota$ is the unit of $L_X$, there is a unique morphism $\chi : A \to X$ over $\operatorname{Spec} k$ with $p$ followed by $\chi$ equal to $\varphi$ and $\chi$ a homomorphism from $L$ to $L_X$.
--
--   This is the existence of the quotient of a fake elliptic curve by a $\Lambda$-stable finite flat subgroup scheme killed by an integer $n$ invertible on the base, in the form of a complete package: the quotient abelian surface with its quaternionic action and trace condition, the dual pair of isogenies $p$, $\psi$ with $\psi p = [n]$ and $p\psi = [n]$, the identification of $\ker p$ with the given subgroup, and the universal property; no level structure is produced, each consumer supplying its own. It is the common engine behind the constructions of level isogenies between fake elliptic curves with extra level and of Atkin–Lehner quotients in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_core_of_isAlgClosed.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_quotient_core_of_isAlgClosed
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type) [Field k] [IsAlgClosed k] (E₀ : FakeEllipticCurve Λ N k) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (n : ℕ) (hn : (n : k) ≠ 0)
    (K₀ : Scheme.{0}) (ι : K₀ ⟶ E₀.A) (hι_closed : IsClosedImmersion ι)
    (hι_finite : IsFinite (ι ≫ E₀.f)) (hι_flat : Flat (ι ≫ E₀.f)) (hι_fp : LocallyOfFinitePresentation (ι ≫ E₀.f))
    (hK_one : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough ι (E₀.L.one t))
    (hK_sub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E₀.f),
      FactorsThrough ι P → FactorsThrough ι Q → FactorsThrough ι (E₀.L.mul t P Q) ∧ FactorsThrough ι (E₀.L.inv t P))
    (hK_stable : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
      FactorsThrough ι P → FactorsThrough ι (pushPt (E₀.act x) (E₀.act_over x) P))
    (hK_torsion : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
      FactorsThrough ι P → nsmulPt E₀.L t n P = E₀.L.one t) :
    ∃ (A : Scheme.{0}) (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) (act : ↥Λ → (A ⟶ A))
      (hact : ∀ x : ↥Λ, act x ≫ f = f)
      (p : E₀.A ⟶ A) (hp : p ≫ f = E₀.f) (ψ : A ⟶ E₀.A) (hψ : ψ ≫ E₀.f = f),

      L.IsCommutative ∧
      AbelianSchemePropertyBundle k f ∧
      (∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = 2) ∧
      (∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
        pushPt (act x) (hact x) (L.mul t P Q) = L.mul t (pushPt (act x) (hact x) P) (pushPt (act x) (hact x) Q)) ∧
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 A) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x) ∧
      (∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f),
        pushPt (act (x + y)) (hact (x + y)) P = L.mul t (pushPt (act x) (hact x) P) (pushPt (act y) (hact y) P)) ∧
      (∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k')
        (V : Type) [AddCommGroup V] [Module k' V] [Module.Finite k' V] (τ : V → SchemeHomOver (tangentBase k' sk) f),
        Function.Injective τ →
        (∀ P : SchemeHomOver (tangentBase k' sk) f, P ∈ Set.range τ ↔ IsTangentVector L k' sk P) →
        (∀ v w : V, τ (v + w) = L.mul (tangentBase k' sk) (τ v) (τ w)) →
        (∀ (c : k') (v : V), (τ (c • v)).1 = tangentScale k' c ≫ (τ v).1) →
        ∀ (m : ↥Λ) (Φ : V →ₗ[k'] V), (∀ v : V, τ (Φ v) = pushPt (act m) (hact m) (τ v)) →
        ∀ n' : ℤ, (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n' : ℚ) : ℍ[ℚ, a, b]) →
          LinearMap.trace k' V Φ = (n' : k')) ∧

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E₀.f),
        mapPt p hp (E₀.L.mul t P Q) = L.mul t (mapPt p hp P) (mapPt p hp Q)) ∧
      (∀ x : ↥Λ, E₀.act x ≫ p = p ≫ act x) ∧
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧ Etale p ∧
      (∀ y : ↥A, p.finrank y = (ι ≫ E₀.f).finrank (f.base y)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        mapPt p hp P = L.one t ↔ FactorsThrough ι P) ∧

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
        mapPt ψ hψ (L.mul t P Q) = E₀.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
      (∀ x : ↥Λ, act x ≫ ψ = ψ ≫ E₀.act x) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        mapPt ψ hψ (mapPt p hp P) = nsmulPt E₀.L t n P) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t f),
        mapPt p hp (mapPt ψ hψ Q) = nsmulPt L t n Q) ∧

      (∀ (X : Scheme.{0}) (gX : X ⟶ Spec (CommRingCat.of k)) (LX : RelativeGroupLaw k gX) (φ : E₀.A ⟶ X) (hφ : φ ≫ gX = E₀.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E₀.f),
          mapPt φ hφ (E₀.L.mul t P Q) = LX.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
          FactorsThrough ι P → mapPt φ hφ P = LX.one t) →
        ∃! χ : SchemeHomOver f gX, p ≫ χ.1 = φ ∧
          ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (u v : SchemeHomOver t f),
            mapPt χ.1 χ.2 (L.mul t u v) = LX.mul t (mapPt χ.1 χ.2 u) (mapPt χ.1 χ.2 v)) := by sorry
