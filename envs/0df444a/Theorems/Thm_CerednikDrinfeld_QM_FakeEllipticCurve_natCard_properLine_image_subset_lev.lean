-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.natCard_properLine_image_subset_lev
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/2a20a4e5-9f9d-5bb0-9df7-80bcd8dc8962
-- title:
--   One proper Λ-line inside the level structure iff ℓ ∣ N
-- statement:
--   Let $q \neq q'$ be primes, let $a,b \in \mathbb{Q}$ satisfy `IsIndefiniteRamifiedExactlyAt`, i.e. $0 < a$ or $0 < b$ and, for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit precisely when $q \in v$ or $q' \in v$; let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order (containing $1$, closed under multiplication, $\mathbb{Q}$-spanning, finitely generated) and maximal among orders. Let $N \neq 0$, let $\ell$ be a prime distinct from $q$ and $q'$, let $k$ be an algebraically closed field with $\ell \neq 0$ and $N \neq 0$ in $k$, and let $E$ be a fake elliptic curve of level $N$ over $k$ in the sense of `FakeEllipticCurve` (a scheme $E.A$ proper and smooth over $\operatorname{Spec} k$ with connected two-dimensional fibres, a commutative relative group law $E.L$, an action $m \mapsto E.act\,m$ of $\Lambda$ by endomorphisms over the base, and a level morphism $E.lev$ into $E.A$). Let $P_0$ be a $k$-point of $E.A$, i.e. a morphism $\operatorname{Spec} k \to E.A$ over $\operatorname{Spec} k$, such that: $\ell P_0$ is the identity section; every $k$-point $P$ with $\ell P$ the identity section is $E.act\,m$ applied to $P_0$ for some $m \in \Lambda$; and $E.act\,m$ applied to $P_0$ is the identity section exactly when $m \in \ell\Lambda$. Then the number of $\mathbb{Z}$-submodules $J$ of $\mathbb{H}[\mathbb{Q},a,b]$ with $J \subseteq \Lambda$, $\ell\Lambda \subseteq J$, $\Lambda J \subseteq J$, $J \not\subseteq \ell\Lambda$ and $J \neq \Lambda$, and such that for every $m \in \Lambda \cap J$ the point $E.act\,m$ applied to $P_0$ factors through $E.lev$ (some $\operatorname{Spec} k \to E.C$ composed with $E.lev$ gives it), equals $1$ if $\ell \mid N$ and $0$ otherwise.
--
--   This is the local count, at a prime $\ell$ away from the ramification of the quaternion algebra, of the proper $\Lambda$-stable lines in the $\ell$-torsion of a fake elliptic curve whose associated points all lie in the level-$N$ structure: there is exactly one when $\ell$ divides $N$ and none otherwise. It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_enum`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_enum) in the analysis of integral models of Shimura curves attached to indefinite quaternion algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.natCard_properLine_image_subset_lev
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (k : Type) [Field k] [IsAlgClosed k] (hℓk : (ℓ : k) ≠ 0) (hNk : (N : k) ≠ 0)
    (E : FakeEllipticCurve Λ N k)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f)
    (hP₀ : nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) ℓ P₀ = E.L.one (𝟙 (Spec (CommRingCat.of k))))
    (hgen : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f,
      nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) ℓ P = E.L.one (𝟙 (Spec (CommRingCat.of k))) →
        ∃ m : ↥Λ, P = pushPt (E.act m) (E.act_over m) P₀)
    (hann : ∀ m : ↥Λ, pushPt (E.act m) (E.act_over m) P₀ = E.L.one (𝟙 (Spec (CommRingCat.of k))) ↔
      ∃ m' : ↥Λ, (m : ℍ[ℚ, a, b]) = ((ℓ : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b])) :
    Nat.card {J : Submodule ℤ ℍ[ℚ, a, b] //
        (J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
          (∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J ≠ Λ) ∧
        ∀ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J → FactorsThrough E.lev (pushPt (E.act m) (E.act_over m) P₀)} =
      (if ℓ ∣ N then 1 else 0) := by sorry
