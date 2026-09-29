-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_action_comp_eq_comp_of_isPullback_of_abelianSchemePropertyBundle
-- name    : CerednikDrinfeld.QM.exists_action_comp_eq_comp_of_isPullback_of_abelianSchemePropertyBundle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/c412e18f-acee-58c5-8b32-0540023e95cf
-- title:
--   Quaternionic action on the generic fibre extends to the abelian scheme
-- statement:
--   Fix $a,b\in\mathbb{Q}$ and a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$. Let $R$ be a discrete valuation domain with fraction field $K$, let $f\colon\mathcal{A}\to\operatorname{Spec}R$ carry a relative group law $L$ (a group structure on the sets $\{\varphi\colon T\to\mathcal{A}\mid \varphi\,;f=t\}$ for all $t\colon T\to\operatorname{Spec}R$, natural in $T$) and satisfy `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, each fibre of the underlying map is connected, and a relative group law over $R$ exists. Let $f_P\colon P\to\operatorname{Spec}K$ carry a relative group law $L_P$, and let $g\colon P\to\mathcal{A}$ make the square with $f$, $f_P$ and $\operatorname{Spec}$ of $R\to K$ cartesian, and be a homomorphism on points: composition with $g$ takes $L_P$-products to $L$-products after base change. Assume given $\mathrm{act}(x)\colon P\to P$ for $x\in\Lambda$, each over $\operatorname{Spec}K$, each a homomorphism on $T$-valued points, with $\mathrm{act}(1)=\mathrm{id}_P$ when $1\in\Lambda$, $\mathrm{act}(xy)=\mathrm{act}(y)\,;\mathrm{act}(x)$ whenever $xy\in\Lambda$, and $\mathrm{act}(x+y)$ equal pointwise to the $L_P$-product of $\mathrm{act}(x)$ and $\mathrm{act}(y)$. Then there are $\mathrm{act}'(x)\colon\mathcal{A}\to\mathcal{A}$ over $f$ with $\mathrm{act}(x)\,;g=g\,;\mathrm{act}'(x)$; each $\mathrm{act}'(x)$ is the unique endomorphism over $f$ with this property; and $\mathrm{act}'$ satisfies the same four laws with respect to $L$: homomorphism on $T$-points, unit, anti-multiplicativity in diagrammatic order, and additivity.
--
--   This is the Néron mapping property step transporting a quaternionic action from the generic fibre to an abelian scheme over a discrete valuation ring, in the form used for fake elliptic curves. It is the engine behind the statements producing a `FakeEllipticCurve` over $R$ pulling back to the given one over $K$, and hence behind the integral models of Shimura curves used in the Čerednik–Drinfel'd comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_action_comp_eq_comp_of_isPullback_of_abelianSchemePropertyBundle.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.exists_action_comp_eq_comp_of_isPullback_of_abelianSchemePropertyBundle
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    {𝒜 : Scheme.{u}} {f : 𝒜 ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (h𝒜 : AbelianSchemePropertyBundle R f)
    {P : Scheme.{u}} {fP : P ⟶ Spec (CommRingCat.of K)} (LP : RelativeGroupLaw K fP)
    (g : P ⟶ 𝒜) (hg : CategoryTheory.IsPullback g fP f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t' fP),
      (LP.mul t' x y).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨x.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    (act : ↥Λ → (P ⟶ P)) (act_over : ∀ x : ↥Λ, act x ≫ fP = fP)
    (act_hom : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (u v : SchemeHomOver t fP),
      pushPt (act x) (act_over x) (LP.mul t u v) =
        LP.mul t (pushPt (act x) (act_over x) u) (pushPt (act x) (act_over x) v))
    (act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 P)
    (act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x)
    (act_add : ∀ (x y : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (u : SchemeHomOver t fP),
      pushPt (act (x + y)) (act_over (x + y)) u =
        LP.mul t (pushPt (act x) (act_over x) u) (pushPt (act y) (act_over y) u)) :
    ∃ (act' : ↥Λ → (𝒜 ⟶ 𝒜)) (act'_over : ∀ x : ↥Λ, act' x ≫ f = f),
      (∀ x : ↥Λ, act x ≫ g = g ≫ act' x) ∧
      (∀ (x : ↥Λ) (ψ : 𝒜 ⟶ 𝒜), ψ ≫ f = f → act x ≫ g = g ≫ ψ → ψ = act' x) ∧
      (∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (u v : SchemeHomOver t f),
        pushPt (act' x) (act'_over x) (L.mul t u v) =
          L.mul t (pushPt (act' x) (act'_over x) u) (pushPt (act' x) (act'_over x) v)) ∧
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act' ⟨1, h⟩ = 𝟙 𝒜) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        act' ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act' y ≫ act' x) ∧
      (∀ (x y : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (u : SchemeHomOver t f),
        pushPt (act' (x + y)) (act'_over (x + y)) u =
          L.mul t (pushPt (act' x) (act'_over x) u) (pushPt (act' y) (act'_over y) u)) := by sorry
