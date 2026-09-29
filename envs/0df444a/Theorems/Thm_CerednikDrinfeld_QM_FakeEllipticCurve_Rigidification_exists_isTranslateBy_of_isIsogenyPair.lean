-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isTranslateBy_of_isIsogenyPair
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isTranslateBy_of_isIsogenyPair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/ee919a6a-bd90-5880-ac58-6395d02cf448
-- title:
--   Translating a rigidification by a self-isogeny of A₀
-- statement:
--   Fix a prime $r$, a commutative ring $\mathcal O$ with an element $\pi$, an $\mathcal O$-algebra $O^{nr}$, rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of $\mathbb H[\mathbb Q,a,b]$ and a natural number $N$, and assume $\Lambda$ contains the image of every integer $m$ (hypothesis `hΛℤ`). Let $A_0$ be a fake elliptic curve with data $\Lambda,N$ over $O^{nr}/(\pi)$, let $e_\gamma,e_\gamma'$ be endomorphisms of the scheme $A_0.A$ with $e_\gamma$ a morphism over the base ($e_\gamma$ followed by $A_0.f$ is $A_0.f$), and let $d_\gamma$ be a natural number such that $(e_\gamma,e_\gamma')$ is an isogeny pair of degree $r^{d_\gamma}$ on $A_0$: both maps lie over the base, both are additive for the relative group law on $T$-points, both commute with the $\Lambda$-action, and each composite is the action of the scalar $r^{d_\gamma}$ whenever that scalar lies in $\Lambda$; assume further that $e_\gamma$ preserves the level, i.e. it carries points factoring through $A_0.\mathrm{lev}$ to points factoring through $A_0.\mathrm{lev}$. Let $B$ be a commutative $\mathcal O$-algebra, $\psi:O^{nr}\to B$ an $\mathcal O$-algebra map, $E$ a fake elliptic curve with data $\Lambda,N$ over $B$, and $\varrho$ a rigidification of $E$ along $\psi$ relative to $A_0$ (a reduction $E_b$ of $E$ modulo $\pi$ together with the cartesian comparison $g_b$, a pullback $A_b$ of $A_0$ along the induced map of residue rings with comparison $g_A$, and an isogeny pair $\varphi,\varphi'$ of degree $r^{d}$ between $E_b$ and $A_b$ with $\varphi$ over the base and level-preserving). The assertion is that there exists a rigidification $\rho_2$ of $E$ along $\psi$ with two properties. First, $\rho_2$ is a translate of $\varrho$ by $e_\gamma$ in the sense of `IsTranslateBy`: there are morphisms $u:\rho_2.E_b.A\to\varrho.E_b.A$ and $u_A:\rho_2.A_b.A\to\varrho.A_b.A$ satisfying the predicate `IsComparison` for $\varrho,\rho_2$, and an endomorphism $e_{\gamma b}$ of $\varrho.A_b.A$ over the base with $e_{\gamma b}$ followed by $\varrho.g_A$ equal to $\varrho.g_A$ followed by $e_\gamma$, such that for some natural numbers $i,j$ the composite $u$, $\varrho.\varphi$, $e_{\gamma b}$, the action of $r^i$ agrees with the composite $\rho_2.\varphi$, $u_A$, the action of $r^j$. Second, $\rho_2$ inherits extra-level compatibilities: for every $\ell$ and every extra level $K_0$ on $A_0$ (a closed immersion $\mathrm{lev}_K$ onto an $\ell$-torsion, $\Lambda$-stable subgroup disjoint from $A_0.\mathrm{lev}$, finite flat of rank $\ell^2$ with geometric fibres $(\mathbb Z/\ell)^2$) whose factorisation property is preserved by $e_\gamma$, and every extra level $C$ on $E$, if for all $T$-points $R$ of $\varrho.E_b$ over $B/(\pi)$ whose image under $\varrho.g_b$ factors through $C.\mathrm{lev}_K$ the composite of $R$ with $\varrho.\varphi$ and then $\varrho.g_A$ factors through $K_0.\mathrm{lev}_K$, then the same implication holds with $\varrho$ replaced by $\rho_2$.
--
--   This is the step that makes self-isogenies of the fixed fake elliptic curve $A_0$ over $O^{nr}/(\pi)$ act on rigidifications of a fake elliptic curve over an $\mathcal O$-algebra, in the Čerednik–Drinfeld description of the special fibre: the translated rigidification is produced together with the bookkeeping needed to compare it with the original one and to carry extra level structures along. It is used in the results constructing the twisted action on rigidifications and comparing translated level data with characters and height normalisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isTranslateBy_of_isIsogenyPair.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isTranslateBy_of_isIsogenyPair
    {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    (eγ eγ' : A₀.A ⟶ A₀.A) (heγ : eγ ≫ A₀.f = A₀.f) (dγ : ℕ)
    (hpair : FakeEllipticCurve.IsIsogenyPair (r ^ dγ) A₀ A₀ eγ eγ')
    (hlev : FakeEllipticCurve.PreservesLevel A₀ A₀ eγ heγ)
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E : FakeEllipticCurve Λ N B}
    (ϱ : FakeEllipticCurve.Rigidification r π A₀ ψ E) :
    ∃ ρ₂ : FakeEllipticCurve.Rigidification r π A₀ ψ E,
      FakeEllipticCurve.Rigidification.IsTranslateBy hΛℤ eγ ϱ ρ₂ ∧
      (∀ (ℓ : ℕ) (K₀ : A₀.ExtraLevel ℓ),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (R : SchemeHomOver t A₀.f),
            FactorsThrough K₀.levK R → FactorsThrough K₀.levK (mapPt eγ heγ R)) →
        ∀ (C : E.ExtraLevel ℓ),
          (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ϱ.Eb.f),
              (∃ R₀ : T ⟶ C.K, R₀ ≫ C.levK = R.1 ≫ ϱ.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ϱ.φ) ≫ ϱ.gA) →
          (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ρ₂.Eb.f),
              (∃ R₀ : T ⟶ C.K, R₀ ≫ C.levK = R.1 ≫ ρ₂.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ρ₂.φ) ≫ ρ₂.gA)) := by sorry
