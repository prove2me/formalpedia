-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_of_comp_eq_act_of_not_isIsogenyPair
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_of_comp_eq_act_of_not_isIsogenyPair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/3059c698-ebb2-544a-849e-7564827076cf
-- title:
--   Extra level at ℓ from the kernel of f on A₀[ℓ]
-- statement:
--   Let $r,\bar r$ be distinct primes, $N$ a nonzero natural number, and $a,b$ rationals such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b r rbar`: $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $r$ or $\bar r$. Let $\Lambda$ be a maximal order in $\mathbb{H}[\mathbb{Q},a,b]$ (an order, maximal among orders) containing every rational integer, let $k_0$ be an algebraically closed field of characteristic $r$, and let $A_0$ be a fake elliptic curve over $k_0$ of level data $\Lambda,N$ (a scheme with structure morphism $A_0.f$, a commutative relative group law $A_0.L$, abelian-scheme properties, two-dimensional fibres, a $\Lambda$-action $A_0.act$ and a level morphism $A_0.lev$). Let $\ell$ be a prime different from $r$ and $\bar r$, let $e\in\mathbb{N}$, and let $f,f' : A_0.A \to A_0.A$ be morphisms over the base which are additive on $T$-points for $A_0.L$, commute with the action of every element of $\Lambda$, and satisfy $f\circ f' = f'\circ f = A_0.act(r^e\ell)$. Assume further that for no $j\in\mathbb{N}$ and no $\psi$ is $(f,\psi)$, respectively $(f',\psi)$, an `IsIsogenyPair` of degree $r^j$ from $A_0$ to $A_0$ (that is, a pair of base-preserving, additive, $\Lambda$-equivariant morphisms composing to $A_0.act(r^j)$ in both orders), and that any $T$-point $P$ of $A_0$ which factors through $A_0.lev$, is killed by $\ell$ and satisfies $f(P)=0$ is already the identity section. Then there is an extra level structure $C_0 : A_0.\mathrm{ExtraLevel}\ \ell$ — a closed immersion $C_0.levK$ into $A_0.A$ whose points form a $\Lambda$-stable subgroup killed by $\ell$, disjoint from $A_0.lev$, finite flat of finite presentation of rank $\ell^2$ with geometric fibres $(\mathbb{Z}/\ell)^2$ — such that for every base-scheme morphism $t : T \to \operatorname{Spec} k_0$ and every $T$-point $P$ of $A_0$ one has: $P$ factors through $C_0.levK$ if and only if $\ell P$ is the identity section and $f(P)$ is the identity section; and if $\ell P$ is the identity section then $f'(P)$ factors through $C_0.levK$.
--
--   The statement identifies the $\ell$-part of the kernel of an endomorphism of degree $r^e\ell$ of a fake elliptic curve in characteristic $r$ as an auxiliary level-$\ell$ structure, the non-degeneracy hypotheses ruling out that this kernel is trivial or all of $A_0[\ell]$. It feeds the construction of a level-$\ell$ isogeny between fake elliptic curves with extra level structure used in the Čerednik–Drinfeld analysis of Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_of_comp_eq_act_of_not_isIsogenyPair.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_of_comp_eq_act_of_not_isIsogenyPair
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
    (hff' : f ≫ f' = A₀.act ⟨(((r ^ e * ℓ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (hf'f : f' ≫ f = A₀.act ⟨(((r ^ e * ℓ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    (hf_not : ∀ (j : ℕ) (ψ : A₀.A ⟶ A₀.A), ¬ FakeEllipticCurve.IsIsogenyPair (r ^ j) A₀ A₀ f ψ)
    (hf'_not : ∀ (j : ℕ) (ψ : A₀.A ⟶ A₀.A), ¬ FakeEllipticCurve.IsIsogenyPair (r ^ j) A₀ A₀ f' ψ)
    (hdisj : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P : SchemeHomOver t A₀.f),
      FactorsThrough A₀.lev P → nsmulPt A₀.L t ℓ P = A₀.L.one t → mapPt f hf P = A₀.L.one t → P = A₀.L.one t) :
    ∃ C₀ : A₀.ExtraLevel ℓ,
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P : SchemeHomOver t A₀.f),
        (FactorsThrough C₀.levK P ↔ (nsmulPt A₀.L t ℓ P = A₀.L.one t ∧ mapPt f hf P = A₀.L.one t)) ∧
        (nsmulPt A₀.L t ℓ P = A₀.L.one t → FactorsThrough C₀.levK (mapPt f' hf' P)) := by sorry
