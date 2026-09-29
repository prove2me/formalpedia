-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_forall_mapPt_eq_one_iff_torsionPrime_of_comp_eq_act_of_not_isIsogenyPair
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.forall_mapPt_eq_one_iff_torsionPrime_of_comp_eq_act_of_not_isIsogenyPair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/d5001083-b1c4-58a1-9335-d2ab38ba7ceb
-- title:
--   The ̄ r-part of ker f is exactly A₀[mathfrak P_{̄ r}]
-- statement:
--   Let $r\neq\bar r$ be primes and $N$ a nonzero natural number, and let $a,b\in\mathbb Q$ be such that $\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b r rbar`, i.e. $0<a$ or $0<b$, and for each height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the completed algebra $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ has all nonzero elements invertible precisely when $v$ contains $r$ or $\bar r$. Let $\Lambda$ be a $\mathbb Z$-submodule that is a maximal order (an order maximal among orders) and contains every rational integer, let $k_0$ be an algebraically closed field of characteristic $r$, and let $A_0$ be a fake elliptic curve of level $N$ over $k_0$ for $\Lambda$: a scheme $A$ over $\operatorname{Spec} k_0$ with commutative relative group law $L$, the abelian-scheme property bundle, two-dimensional fibres, a $\Lambda$-action by endomorphisms over the base which are additive and compatible with $1$, products and sums and satisfy the trace condition, together with the remaining level data. Let $e\in\mathbb N$ and let $f,f'$ be endomorphisms of $A_0.A$ over $k_0$, each additive on $T$-points for $L$ and commuting with every $A_0.\mathrm{act}\,m$, with $f\circ f'=f'\circ f$ equal to the action of the integer $r^e\bar r$, and assume that neither $f$ nor $f'$ is part of an `IsIsogenyPair (r ^ j)` for any $j$ and any partner $\psi$. Then for every scheme $T$, every $t:T\to\operatorname{Spec} k_0$ and every $T$-point $P$ of $A_0.A$ over $t$: (i) if $\mathrm{act}\,m$ kills $P$ for every $m\in\Lambda$ with $m\,\bar m=\bar r n$ for some integer $n$, then $f$ kills $P$; (ii) if $\bar r\cdot P$ (iterated group law) is the identity section and $f$ kills $P$, then every such $m$ kills $P$; (iii) if $\bar r\cdot P$ is the identity section, then every such $m$ kills $f'(P)$.
--
--   In the classical language this identifies, for an endomorphism of reduced degree $r^e\bar r$ of a fake elliptic curve in characteristic $r$ whose kernel contains no $r$-power isogeny factor, the $\bar r$-torsion part of $\ker f$ with the kernel $A_0[\mathfrak P_{\bar r}]$ of the two-sided prime of the maximal order above $\bar r$, and shows that $f'$ maps $A_0[\bar r]$ into that kernel. It is used in the construction of the Atkin–Lehner quotient of $A_0$ by an isogeny pair, in the Čerednik–Drinfeld analysis of Shimura curves at a ramified prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_forall_mapPt_eq_one_iff_torsionPrime_of_comp_eq_act_of_not_isIsogenyPair.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.forall_mapPt_eq_one_iff_torsionPrime_of_comp_eq_act_of_not_isIsogenyPair
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] [CharP k₀ r] (A₀ : FakeEllipticCurve Λ N k₀) (e : ℕ)
    (f f' : A₀.A ⟶ A₀.A) (hf : f ≫ A₀.f = A₀.f) (hf' : f' ≫ A₀.f = A₀.f)
    (hf_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      mapPt f hf (A₀.L.mul t P Q) = A₀.L.mul t (mapPt f hf P) (mapPt f hf Q))
    (hf'_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      mapPt f' hf' (A₀.L.mul t P Q) = A₀.L.mul t (mapPt f' hf' P) (mapPt f' hf' Q))
    (hf_lin : ∀ m : ↥Λ, A₀.act m ≫ f = f ≫ A₀.act m) (hf'_lin : ∀ m : ↥Λ, A₀.act m ≫ f' = f' ≫ A₀.act m)
    (hff' : f ≫ f' = A₀.act ⟨(((r ^ e * rbar : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (hf'f : f' ≫ f = A₀.act ⟨(((r ^ e * rbar : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    (hf_not : ∀ (j : ℕ) (ψ : A₀.A ⟶ A₀.A), ¬ FakeEllipticCurve.IsIsogenyPair (r ^ j) A₀ A₀ f ψ)
    (hf'_not : ∀ (j : ℕ) (ψ : A₀.A ⟶ A₀.A), ¬ FakeEllipticCurve.IsIsogenyPair (r ^ j) A₀ A₀ f' ψ) :
    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P : SchemeHomOver t A₀.f),
      ((∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((rbar : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
            pushPt (A₀.act m) (A₀.act_over m) P = A₀.L.one t) → mapPt f hf P = A₀.L.one t) ∧
      (nsmulPt A₀.L t rbar P = A₀.L.one t → mapPt f hf P = A₀.L.one t →
        (∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((rbar : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
            pushPt (A₀.act m) (A₀.act_over m) P = A₀.L.one t)) ∧
      (nsmulPt A₀.L t rbar P = A₀.L.one t →
        (∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((rbar : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
            pushPt (A₀.act m) (A₀.act_over m) (mapPt f' hf' P) = A₀.L.one t)) := by sorry
