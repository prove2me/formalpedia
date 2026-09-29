-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogenyVia_isIsogenyPair_comp_eq_of_comp_eq_act_of_not_isIsogenyPair
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogenyVia_isIsogenyPair_comp_eq_of_comp_eq_act_of_not_isIsogenyPair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/ad754127-7594-5b84-9fc4-eedac1d2540f
-- title:
--   Factoring a level-preserving endomorphism through an ℓ-level structure
-- statement:
--   Let $r,\bar r$ be distinct primes, $N\ge 1$, and let $a,b\in\mathbb{Q}$ be such that `IsIndefiniteRamifiedExactlyAt a b r rbar` holds: $a>0$ or $b>0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $r\in v$ or $\bar r\in v$. Let $\Lambda\subset\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is a maximal order and contains every rational integer, let $k_0$ be an algebraically closed field of characteristic $r$, and let $A_0$ be a fake elliptic curve over $k_0$ of level $N$ with $\Lambda$-action (a two-dimensional abelian scheme with commutative relative group law $A_0.L$, $\Lambda$-action `A₀.act`, and level map `A₀.lev`). Let $\ell$ be a prime different from $r$ and $\bar r$, let $e\in\mathbb{N}$, and let $f,f':A_0\to A_0$ be morphisms over $k_0$ which are homomorphisms for $A_0.L$ on $T$-points, commute with every `A₀.act m`, satisfy $f\circ f'=f'\circ f=$ `A₀.act` of the integer $r^e\ell$, and such that $f$ preserves level: every $T$-point of $A_0$ factoring through `A₀.lev` is carried by $f$ to such a point. Assume further that for no $j\in\mathbb{N}$ and no $\psi:A_0\to A_0$ is $(f,\psi)$, respectively $(f',\psi)$, an isogeny pair of degree $r^j$ in the sense of `IsIsogenyPair`, and that (hypothesis `hdisj`) any $T$-point $P$ of $A_0$ factoring through `A₀.lev` with $\ell P$ the unit and $f\circ P$ the unit is itself the unit. Then there exist an extra level structure $C_0$ on $A_0$ of order $\ell$ (a closed immersion into $A_0$ whose $T$-points form a $\Lambda$-stable subgroup killed by $\ell$, meeting the image of `A₀.lev` only in the unit, finite flat of finite presentation with fibre rank $\ell^2$ and geometric fibres isomorphic to $(\mathbb{Z}/\ell)^2$), a fake elliptic curve $A_{0s}$ over $k_0$ of the same type, morphisms $a_s:A_0\to A_{0s}$ and $a_s':A_{0s}\to A_0$ over $k_0$, a natural number $k_s$, and morphisms $b_s:A_{0s}\to A_0$ over $k_0$ and $b_s':A_0\to A_{0s}$, such that $(a_s,a_s')$ exhibits $A_{0s}$ as the quotient of $(A_0,C_0)$ by an $\ell$-level isogeny in the sense of `IsLevelIsogenyVia` (both maps additive and $\Lambda$-equivariant, the composites equal to the action of $\ell$, the kernel of $a_s$ on $T$-points exactly the points factoring through $C_0$, and $a_s$ level-preserving), $(b_s,b_s')$ is an isogeny pair of degree $r^{k_s}$ from $A_{0s}$ to $A_0$, $b_s$ preserves level, and $a_s$ followed by $b_s$ equals $f$.
--
--   This is the factorisation step in the quaternionic Hecke-correspondence dictionary for fake elliptic curves in characteristic $r$: an endomorphism whose norm is $r^e\ell$ and which is not, up to a partner, of $r$-power degree is split as an $\ell$-level isogeny onto a second fake elliptic curve followed by a level-preserving isogeny of $r$-power degree. It is used in the construction of the Hecke dictionary compatible with the Rosati involution on the endomorphism side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogenyVia_isIsogenyPair_comp_eq_of_comp_eq_act_of_not_isIsogenyPair.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogenyVia_isIsogenyPair_comp_eq_of_comp_eq_act_of_not_isIsogenyPair
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] [CharP k₀ r] (A₀ : FakeEllipticCurve Λ N k₀)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓr : ℓ ≠ r) (hℓrbar : ℓ ≠ rbar) (e : ℕ)
    (f f' : A₀.A ⟶ A₀.A) (hf : f ≫ A₀.f = A₀.f) (hf' : f' ≫ A₀.f = A₀.f)
    (hf_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      mapPt f hf (A₀.L.mul t P Q) = A₀.L.mul t (mapPt f hf P) (mapPt f hf Q))
    (hf'_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      mapPt f' hf' (A₀.L.mul t P Q) = A₀.L.mul t (mapPt f' hf' P) (mapPt f' hf' Q))
    (hf_lin : ∀ m : ↥Λ, A₀.act m ≫ f = f ≫ A₀.act m) (hf'_lin : ∀ m : ↥Λ, A₀.act m ≫ f' = f' ≫ A₀.act m)
    (hf_lev : FakeEllipticCurve.PreservesLevel A₀ A₀ f hf)
    (hff' : f ≫ f' = A₀.act ⟨(((r ^ e * ℓ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (hf'f : f' ≫ f = A₀.act ⟨(((r ^ e * ℓ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    (hf_not : ∀ (j : ℕ) (ψ : A₀.A ⟶ A₀.A), ¬ FakeEllipticCurve.IsIsogenyPair (r ^ j) A₀ A₀ f ψ)
    (hf'_not : ∀ (j : ℕ) (ψ : A₀.A ⟶ A₀.A), ¬ FakeEllipticCurve.IsIsogenyPair (r ^ j) A₀ A₀ f' ψ)
    (hdisj : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P : SchemeHomOver t A₀.f),
      FactorsThrough A₀.lev P → nsmulPt A₀.L t ℓ P = A₀.L.one t → mapPt f hf P = A₀.L.one t → P = A₀.L.one t) :
    ∃ (C₀ : A₀.ExtraLevel ℓ) (A₀s : FakeEllipticCurve Λ N k₀)
      (as : A₀.A ⟶ A₀s.A) (has : as ≫ A₀s.f = A₀.f) (as' : A₀s.A ⟶ A₀.A) (has' : as' ≫ A₀.f = A₀s.f)
      (ks : ℕ) (bs : A₀s.A ⟶ A₀.A) (hbs : bs ≫ A₀.f = A₀s.f) (bs' : A₀.A ⟶ A₀s.A),
      FakeEllipticCurve.IsLevelIsogenyVia ℓ ⟨A₀, C₀⟩ A₀s as has as' has' ∧
      FakeEllipticCurve.IsIsogenyPair (r ^ ks) A₀s A₀ bs bs' ∧ FakeEllipticCurve.PreservesLevel A₀s A₀ bs hbs ∧
      as ≫ bs = f := by sorry
