-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_forall_section_mapPt_eq_one_iff_torsionPrime_of_comp_eq_act_of_not_forall_mapPt_eq_one
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.forall_section_mapPt_eq_one_iff_torsionPrime_of_comp_eq_act_of_not_forall_mapPt_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/d762bd50-2fd6-5f6d-b9f6-e991c14a1fdf
-- title:
--   Kernel of f on ̄ r-torsion is the P-torsion
-- statement:
--   Fix primes $r,\bar r$, a natural number $N$, rationals $a,b$, and assume `IsIndefiniteRamifiedExactlyAt a b r rbar`: $0<a$ or $0<b$, and for every height-one prime $v$ of the integers of $\mathbb Q$ the algebra $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a division algebra exactly when $v$ contains $r$ or $\bar r$. Let $\Lambda\subset\mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule which is a maximal order (it contains $1$, is closed under multiplication, spans the algebra over $\mathbb Q$, is finitely generated, and is maximal among such), with every integer lying in $\Lambda$. Let $k_0$ be an algebraically closed field with $\bar r\neq 0$ in $k_0$, and let $A_0$ be a fake elliptic curve over $k_0$ of level data $(\Lambda,N)$: a scheme $A_0.A\to\operatorname{Spec}k_0$ that is smooth and proper with connected fibres of topological Krull dimension $2$, carrying a commutative relative group law $A_0.L$ on sections and an action $m\mapsto A_0.\mathrm{act}\,m$ of $\Lambda$ by endomorphisms over the base which is additive and multiplicative in $m$, compatible with the group law, and of prescribed trace on tangent spaces. Let $e\in\mathbb N$ and let $f,f'$ be endomorphisms of $A_0.A$ over $\operatorname{Spec}k_0$ which are homomorphisms for $A_0.L$ on sections over every base $t$, commute with each $A_0.\mathrm{act}\,m$, and satisfy $f\circ f'=f'\circ f=A_0.\mathrm{act}(r^e\bar r)$. Assume further that neither $f$ nor $f'$ kills all $\bar r$-torsion $k_0$-points, i.e. for each of $f,f'$ it fails that every section $Q$ of $A_0.f$ over $\mathrm{id}_{\operatorname{Spec}k_0}$ with $\bar r\cdot Q$ (iterated $A_0.L$-multiplication) equal to the identity section is mapped to the identity section. Then for every $k_0$-point $Q$ of $A_0.A$, writing $\mathfrak P$ for the set of $m\in\Lambda$ with $m\,\overline m=\bar r\,n$ for some integer $n$: (1) if $A_0.\mathrm{act}\,m$ sends $Q$ to the identity section for every $m\in\mathfrak P$, then $f$ sends $Q$ to the identity section; (2) if $\bar r\cdot Q$ is the identity section and $f$ sends $Q$ to the identity section, then every $m\in\mathfrak P$ kills $Q$; (3) if $\bar r\cdot Q$ is the identity section, then every $m\in\mathfrak P$ kills $f'(Q)$.
--
--   On $k_0$-points this says that $\ker f\cap A_0[\bar r]=A_0[\mathfrak P]$ and $f'(A_0[\bar r])\subseteq A_0[\mathfrak P]$, where $\mathfrak P$ is the two-sided prime of the maximal order $\Lambda$ above the ramified prime $\bar r$; it identifies the $\bar r$-part of the kernel of an endomorphism of reduced norm $r^e\bar r$ with the $\mathfrak P$-torsion. It is used in the analysis of isogeny pairs on fake elliptic curves in characteristic dividing the ramification, feeding [`CerednikDrinfeld.QM.FakeEllipticCurve.forall_mapPt_eq_one_iff_torsionPrime_of_comp_eq_act_of_not_isIsogenyPair`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.forall_mapPt_eq_one_iff_torsionPrime_of_comp_eq_act_of_not_isIsogenyPair).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_forall_section_mapPt_eq_one_iff_torsionPrime_of_comp_eq_act_of_not_forall_mapPt_eq_one.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.forall_section_mapPt_eq_one_iff_torsionPrime_of_comp_eq_act_of_not_forall_mapPt_eq_one
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime]
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (hrk : (rbar : k₀) ≠ 0) (A₀ : FakeEllipticCurve Λ N k₀) (e : ℕ)
    (f f' : A₀.A ⟶ A₀.A) (hf : f ≫ A₀.f = A₀.f) (hf' : f' ≫ A₀.f = A₀.f)
    (hf_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      mapPt f hf (A₀.L.mul t P Q) = A₀.L.mul t (mapPt f hf P) (mapPt f hf Q))
    (hf'_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      mapPt f' hf' (A₀.L.mul t P Q) = A₀.L.mul t (mapPt f' hf' P) (mapPt f' hf' Q))
    (hf_lin : ∀ m : ↥Λ, A₀.act m ≫ f = f ≫ A₀.act m) (hf'_lin : ∀ m : ↥Λ, A₀.act m ≫ f' = f' ≫ A₀.act m)
    (hff' : f ≫ f' = A₀.act ⟨(((r ^ e * rbar : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (hf'f : f' ≫ f = A₀.act ⟨(((r ^ e * rbar : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    (hf_nd : ¬ ∀ Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k₀))) A₀.f,
      nsmulPt A₀.L (𝟙 (Spec (CommRingCat.of k₀))) rbar Q = A₀.L.one (𝟙 (Spec (CommRingCat.of k₀))) →
        mapPt f hf Q = A₀.L.one (𝟙 (Spec (CommRingCat.of k₀))))
    (hf'_nd : ¬ ∀ Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k₀))) A₀.f,
      nsmulPt A₀.L (𝟙 (Spec (CommRingCat.of k₀))) rbar Q = A₀.L.one (𝟙 (Spec (CommRingCat.of k₀))) →
        mapPt f' hf' Q = A₀.L.one (𝟙 (Spec (CommRingCat.of k₀)))) :
    ∀ Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k₀))) A₀.f,
      ((∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((rbar : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
            pushPt (A₀.act m) (A₀.act_over m) Q = A₀.L.one (𝟙 (Spec (CommRingCat.of k₀)))) →
          mapPt f hf Q = A₀.L.one (𝟙 (Spec (CommRingCat.of k₀)))) ∧
      (nsmulPt A₀.L (𝟙 (Spec (CommRingCat.of k₀))) rbar Q = A₀.L.one (𝟙 (Spec (CommRingCat.of k₀))) →
          mapPt f hf Q = A₀.L.one (𝟙 (Spec (CommRingCat.of k₀))) →
        ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((rbar : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
            pushPt (A₀.act m) (A₀.act_over m) Q = A₀.L.one (𝟙 (Spec (CommRingCat.of k₀)))) ∧
      (nsmulPt A₀.L (𝟙 (Spec (CommRingCat.of k₀))) rbar Q = A₀.L.one (𝟙 (Spec (CommRingCat.of k₀))) →
        ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((rbar : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
            pushPt (A₀.act m) (A₀.act_over m) (mapPt f' hf' Q) = A₀.L.one (𝟙 (Spec (CommRingCat.of k₀)))) := by sorry
