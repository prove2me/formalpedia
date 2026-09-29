-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_isPullback_valuationSubring_of_coprime_of_one_mem_of_isPullback_inf
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_of_isPullback_valuationSubring_of_coprime_of_one_mem_of_isPullback_inf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/d3adc216-ed0c-5430-8a66-7f3074e6dd43
-- title:
--   Extending an extra level and ℓ-isogeny over a valuation subring
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and $N\in\mathbb{N}$. Let $\mathcal{O}$ be a valuation subring of $\overline{\mathbb{Q}}$ and $\ell\in\mathbb{N}$ with $\ell$ coprime to $N$, $\ell\in\Lambda$ and $1\in\Lambda$. Let $\mathcal{A},\mathcal{D}$ be fake elliptic curves of level data $(\Lambda,N)$ over $\mathcal{O}$, and $E,d$ such curves over $\overline{\mathbb{Q}}$. Assume a finite extension $K'/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$, a ring map $\iota_0$ from $\mathcal{O}\cap K'$ to $\mathcal{O}$ inducing the inclusion on elements of $\overline{\mathbb{Q}}$, and fake elliptic curves $\mathcal{A}_0,\mathcal{D}_0$ over $\mathcal{O}\cap K'$ with `FakeEllipticCurve.IsPullback` $\iota_0$ $\mathcal{A}_0$ $\mathcal{A}$ and $\iota_0$ $\mathcal{D}_0$ $\mathcal{D}$, i.e. $\mathcal{A},\mathcal{D}$ arise from $\mathcal{A}_0,\mathcal{D}_0$ by a cartesian square compatible with group laws, $\Lambda$-actions and $N$-level. Assume further morphisms $g_E:E.A\to\mathcal{A}.A$ and $g_d:d.A\to\mathcal{D}.A$ making $E,d$ the pullbacks of $\mathcal{A},\mathcal{D}$ along $\operatorname{Spec}$ of $\mathcal{O}\hookrightarrow\overline{\mathbb{Q}}$, each compatible with the relative group laws on points over an arbitrary base, equivariant for every $x\in\Lambda$, and such that a point factors through the $N$-level $E.\mathrm{lev}$ (resp. $d.\mathrm{lev}$) exactly when its image under $g_E$ (resp. $g_d$) factors through $\mathcal{A}.\mathrm{lev}$ (resp. $\mathcal{D}.\mathrm{lev}$). Finally let $K$ be an extra level of $E$ of order $\ell$ — a closed immersion $K\to E.A$, stable under addition, inversion, the unit and the $\Lambda$-action, killed by $\ell$, disjoint from $E.\mathrm{lev}$, finite flat of finite presentation with fibre rank $\ell^2$ and geometric fibres isomorphic to $\mathbb{Z}/\ell\times\mathbb{Z}/\ell$ — and suppose `IsLevelIsogeny` $\ell$ $\langle E,K\rangle$ $d$ holds: there are mutually $\ell$-dual, additive, $\Lambda$-equivariant maps between $E.A$ and $d.A$ over the base whose composites are the actions of $\ell$, with kernel on points exactly the points factoring through $K.\mathrm{levK}$ and carrying $E.\mathrm{lev}$-points to $d.\mathrm{lev}$-points. The conclusion is that there exists an extra level $\mathcal{K}$ of $\mathcal{A}$ of order $\ell$ such that, for every scheme $T$, every $t'$ over $\operatorname{Spec}\overline{\mathbb{Q}}$ and every $T$-point $P$ of $E$ over $t'$, $P$ factors through $K.\mathrm{levK}$ if and only if $P$ followed by $g_E$ factors through $\mathcal{K}.\mathrm{levK}$, and `IsLevelIsogeny` $\ell$ $\langle\mathcal{A},\mathcal{K}\rangle$ $\mathcal{D}$ holds.
--
--   This is the spreading-out step for extra level structures and $\ell$-isogenies of fake elliptic curves: an $\ell$-isogeny with its kernel, given over the fraction field $\overline{\mathbb{Q}}$ of a valuation subring $\mathcal{O}$, is extended over $\mathcal{O}$ together with its kernel subscheme, the generic fibre of the extended kernel being the original one. It feeds the comparison of reductions used in the Čerednik–Drinfeld description of the Shimura curve model, and is cited in the computation of the correspondence on the place map under Frobenius.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_isPullback_valuationSubring_of_coprime_of_one_mem_of_isPullback_inf.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_of_isPullback_valuationSubring_of_coprime_of_one_mem_of_isPullback_inf
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (O : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) (hℓN : Nat.Coprime ℓ N)
    (hℓΛ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ)
    (𝒜 𝒟 : FakeEllipticCurve Λ N ↥O) (E d : FakeEllipticCurve Λ N (AlgebraicClosure ℚ))

    (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K']
    (ι₀ : ↥(O.toSubring ⊓ K'.toSubring) →+* ↥O) (hι₀ : ∀ x : ↥(O.toSubring ⊓ K'.toSubring), (ι₀ x : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ))
    (𝒜₀ 𝒟₀ : FakeEllipticCurve Λ N ↥(O.toSubring ⊓ K'.toSubring))
    (h𝒜₀ : FakeEllipticCurve.IsPullback ι₀ 𝒜₀ 𝒜) (h𝒟₀ : FakeEllipticCurve.IsPullback ι₀ 𝒟₀ 𝒟)

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
    (hgd_lev : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t' d.f),
      FactorsThrough d.lev P ↔ ∃ P₀ : T ⟶ 𝒟.C, P₀ ≫ 𝒟.lev = P.1 ≫ gd)

    (K : E.ExtraLevel ℓ) (hd : IsLevelIsogeny ℓ (⟨E, K⟩ : WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ)) d) :
    ∃ 𝒦 : 𝒜.ExtraLevel ℓ,

      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t' E.f),
          FactorsThrough K.levK P ↔ ∃ P₀ : T ⟶ 𝒦.K, P₀ ≫ 𝒦.levK = P.1 ≫ gE) ∧
      IsLevelIsogeny ℓ (⟨𝒜, 𝒦⟩ : WithExtraLevel Λ N ℓ ↥O) 𝒟 := by sorry
