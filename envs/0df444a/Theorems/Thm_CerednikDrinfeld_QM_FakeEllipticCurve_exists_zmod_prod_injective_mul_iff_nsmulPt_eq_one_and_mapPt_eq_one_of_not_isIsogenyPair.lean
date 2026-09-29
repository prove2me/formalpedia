-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_injective_mul_iff_nsmulPt_eq_one_and_mapPt_eq_one_of_not_isIsogenyPair
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_zmod_prod_injective_mul_iff_nsmulPt_eq_one_and_mapPt_eq_one_of_not_isIsogenyPair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/ab246102-cd69-5c9a-b065-8e9be8185ec7
-- title:
--   Kernel of f on ℓ-torsion is (ℤ/ℓ)²
-- statement:
--   Let $r,\bar r$ be primes with $\bar r\neq r$, let $N$ be a nonzero natural number, and let $a,b\in\mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b r rbar`: $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $r$ or $\bar r$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order maximal among orders and contains every rational integer, let $k_0$ be an algebraically closed field of characteristic $r$, and let $A_0$ be a fake elliptic curve over $k_0$ for $\Lambda$ and level $N$, with structure morphism $A_0.f$, commutative relative group law $A_0.L$ and $\Lambda$-action $A_0.\mathrm{act}$. Let $\ell$ be a prime distinct from $r$ and $\bar r$, let $e\in\mathbb{N}$, and let $f,f':A_0.A\to A_0.A$ be morphisms over $\mathrm{Spec}\,k_0$ such that composition with $f$, resp. $f'$, is additive for $A_0.L$ on the points of $A_0.f$ over every base $t$, such that $A_0.\mathrm{act}(m)$ commutes with $f$ and with $f'$ for every $m\in\Lambda$, and such that both composites $f$ followed by $f'$ and $f'$ followed by $f$ equal $A_0.\mathrm{act}$ of the integer $r^e\ell$. Assume moreover that for no $j\in\mathbb{N}$ and no $\psi:A_0.A\to A_0.A$ does the pair $(f,\psi)$, or the pair $(f',\psi)$, satisfy `IsIsogenyPair` of degree $r^j$ from $A_0$ to $A_0$. Then there is a map $W:\mathbb{Z}/\ell\times\mathbb{Z}/\ell\to A_0(k_0)$, where $A_0(k_0)$ denotes the sections of $A_0.f$ over the identity of $\mathrm{Spec}\,k_0$, which is injective, satisfies $W(i+j)=A_0.L.\mathrm{mul}(W(i),W(j))$, and whose image consists exactly of those points $P$ with $\ell\cdot P$ (iterated multiplication via `nsmulPt`) equal to the identity section and with $P$ followed by $f$ equal to the identity section.
--
--   This identifies the $\ell$-torsion part of the kernel of an endomorphism of norm $r^e\ell$ of a fake elliptic curve in characteristic $r$ as a group isomorphic to $(\mathbb{Z}/\ell)^2$, using that the $\ell$-torsion is a module over $\Lambda/\ell\Lambda\cong M_2(\mathbb{F}_\ell)$ of order $\ell^4$. It is the input to the construction of an auxiliary level-$\ell$ structure, cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_of_comp_eq_act_of_not_isIsogenyPair`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_of_comp_eq_act_of_not_isIsogenyPair).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_injective_mul_iff_nsmulPt_eq_one_and_mapPt_eq_one_of_not_isIsogenyPair.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_zmod_prod_injective_mul_iff_nsmulPt_eq_one_and_mapPt_eq_one_of_not_isIsogenyPair
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
    (hf'_not : ∀ (j : ℕ) (ψ : A₀.A ⟶ A₀.A), ¬ FakeEllipticCurve.IsIsogenyPair (r ^ j) A₀ A₀ f' ψ) :
    ∃ W : ZMod ℓ × ZMod ℓ → SchemeHomOver (𝟙 (Spec (CommRingCat.of k₀))) A₀.f,
      Function.Injective W ∧
      (∀ i j : ZMod ℓ × ZMod ℓ, W (i + j) = A₀.L.mul (𝟙 (Spec (CommRingCat.of k₀))) (W i) (W j)) ∧
      ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k₀))) A₀.f,
        (∃ i : ZMod ℓ × ZMod ℓ, W i = P) ↔
          (nsmulPt A₀.L (𝟙 (Spec (CommRingCat.of k₀))) ℓ P = A₀.L.one (𝟙 (Spec (CommRingCat.of k₀))) ∧
            mapPt f hf P = A₀.L.one (𝟙 (Spec (CommRingCat.of k₀)))) := by sorry
