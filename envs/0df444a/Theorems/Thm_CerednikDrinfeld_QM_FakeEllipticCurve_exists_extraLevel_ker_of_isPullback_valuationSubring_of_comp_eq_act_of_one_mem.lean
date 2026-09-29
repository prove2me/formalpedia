-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_ker_of_isPullback_valuationSubring_of_comp_eq_act_of_one_mem
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_ker_of_isPullback_valuationSubring_of_comp_eq_act_of_one_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/54037b6c-3ed7-57b9-a15c-8fff9972e4cc
-- title:
--   Kernel of an extended ℓ-isogeny as extra level
-- statement:
--   Fix $a,b\in\mathbb{Q}$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and $N\in\mathbb{N}$. Let $O$ be a valuation subring of $\overline{\mathbb{Q}}$ and $\ell\in\mathbb{N}$ with $\gcd(\ell,N)=1$, and assume both $\ell$ and $1$ lie in $\Lambda$. Let $\mathcal{A},\mathcal{D}$ be fake elliptic curves over $O$ and $E,d$ fake elliptic curves over $\overline{\mathbb{Q}}$, in the project's sense: smooth proper schemes with connected fibres over the base, with a commutative relative group law on points of test schemes, fibres of Krull dimension $2$, an action of $\Lambda$ by endomorphisms over the base which are additive on points, multiplicative and additive in the acting element and satisfy a trace condition, together with level-$N$ data $\mathrm{lev}$. Assume $g_E:E.A\to\mathcal{A}.A$ exhibits $E$ as the base change of $\mathcal{A}$ along $O\hookrightarrow\overline{\mathbb{Q}}$ (a pullback square), is additive on points, commutes with the $\Lambda$-actions, and satisfies: a point $P$ of $E$ factors through $E.\mathrm{lev}$ if and only if $P$ composed with $g_E$ factors through $\mathcal{A}.\mathrm{lev}$; assume $g_d:d.A\to\mathcal{D}.A$ satisfies the corresponding pullback, additivity and $\Lambda$-equivariance conditions. Let $K$ be an extra level at $\ell$ on $E$: a closed immersion $K.\mathrm{lev}_K:K.K\to E.A$, finite flat of finite presentation over the base of fibre rank $\ell^2$, whose points are closed under the group law and inversion, contain the unit, are killed by $\ell$, are $\Lambda$-stable, meet the points factoring through $E.\mathrm{lev}$ only in the unit, and form a group isomorphic to $(\mathbb{Z}/\ell)^2$ in every geometric fibre where $\ell$ is invertible. Let $\varphi:E.A\to d.A$ be a morphism over $\overline{\mathbb{Q}}$ such that, on points of every test scheme, $\varphi$ sends $P$ to the unit exactly when $P$ factors through $K.\mathrm{lev}_K$. Finally let $\Phi:\mathcal{A}.A\to\mathcal{D}.A$ be a morphism over $O$, additive on points and commuting with the $\Lambda$-actions, with $\Phi\circ g_E=g_d\circ\varphi$, and let $\Psi:\mathcal{D}.A\to\mathcal{A}.A$ be a morphism over $O$ with $\Psi\circ\Phi=\mathcal{A}.\mathrm{act}(\ell)$ and $\Phi\circ\Psi=\mathcal{D}.\mathrm{act}(\ell)$. Then there is an extra level $\mathcal{K}$ at $\ell$ on $\mathcal{A}$ such that a point $P$ of $E$ factors through $K.\mathrm{lev}_K$ if and only if $P$ composed with $g_E$ factors through $\mathcal{K}.\mathrm{lev}_K$, and such that, for points $P$ of $\mathcal{A}$ over any test scheme over $O$, $\Phi(P)$ is the unit if and only if $P$ factors through $\mathcal{K}.\mathrm{lev}_K$.
--
--   This identifies the scheme-theoretic kernel of a homomorphism $\Phi$ over the valuation ring $O$, extending an $\ell$-isogeny $\varphi$ of fake elliptic curves over $\overline{\mathbb{Q}}$ with kernel $K$, as an extra level-$\ell$ structure on the integral model $\mathcal{A}$ whose geometric fibre is $K$. It feeds the construction of level-$\ell$ isogenies of integral models in the Čerednik–Drinfeld treatment of quaternionic moduli.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_ker_of_isPullback_valuationSubring_of_comp_eq_act_of_one_mem.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_ker_of_isPullback_valuationSubring_of_comp_eq_act_of_one_mem
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (O : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) (hℓN : Nat.Coprime ℓ N) (hℓΛ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ)
    (𝒜 𝒟 : FakeEllipticCurve Λ N ↥O) (E d : FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (gE : E.A ⟶ 𝒜.A) (hgE : CategoryTheory.IsPullback gE E.f 𝒜.f (Spec.map (CommRingCat.ofHom O.subtype)))
    (hgE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ gE =
        (𝒜.L.mul (t' ≫ Spec.map (CommRingCat.ofHom O.subtype))
          ⟨P.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, Q.2]⟩).1)
    (hgE_act : ∀ x : ↥Λ, E.act x ≫ gE = gE ≫ 𝒜.act x)
    (hgE_lev : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t' E.f),
      FactorsThrough E.lev P ↔ ∃ P₀ : T ⟶ 𝒜.C, P₀ ≫ 𝒜.lev = P.1 ≫ gE)
    (gd : d.A ⟶ 𝒟.A) (hgd : CategoryTheory.IsPullback gd d.f 𝒟.f (Spec.map (CommRingCat.ofHom O.subtype)))
    (hgd_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' d.f),
      (d.L.mul t' P Q).1 ≫ gd =
        (𝒟.L.mul (t' ≫ Spec.map (CommRingCat.ofHom O.subtype))
          ⟨P.1 ≫ gd, by rw [Category.assoc, hgd.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gd, by rw [Category.assoc, hgd.w, ← Category.assoc, Q.2]⟩).1)
    (hgd_act : ∀ x : ↥Λ, d.act x ≫ gd = gd ≫ 𝒟.act x)
    (K : E.ExtraLevel ℓ)
    (φ : E.A ⟶ d.A) (hφ : φ ≫ d.f = E.f)
    (hker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
      mapPt φ hφ P = d.L.one t ↔ FactorsThrough K.levK P)
    (Φ : 𝒜.A ⟶ 𝒟.A) (hΦ : Φ ≫ 𝒟.f = 𝒜.f) (hext : gE ≫ Φ = φ ≫ gd)
    (hΦ_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P Q : SchemeHomOver t 𝒜.f),
      mapPt Φ hΦ (𝒜.L.mul t P Q) = 𝒟.L.mul t (mapPt Φ hΦ P) (mapPt Φ hΦ Q))
    (hΦ_act : ∀ x : ↥Λ, 𝒜.act x ≫ Φ = Φ ≫ 𝒟.act x)
    (Ψ : 𝒟.A ⟶ 𝒜.A) (hΨ : Ψ ≫ 𝒜.f = 𝒟.f)
    (hΦΨ : Φ ≫ Ψ = 𝒜.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓΛ⟩)
    (hΨΦ : Ψ ≫ Φ = 𝒟.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓΛ⟩) :
    ∃ 𝒦 : 𝒜.ExtraLevel ℓ,
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t' E.f),
          FactorsThrough K.levK P ↔ ∃ P₀ : T ⟶ 𝒦.K, P₀ ≫ 𝒦.levK = P.1 ≫ gE) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P : SchemeHomOver t 𝒜.f),
          mapPt Φ hΦ P = 𝒟.L.one t ↔ FactorsThrough 𝒦.levK P) := by sorry
