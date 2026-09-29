-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_iff
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_isClosed_range_subset_iff_forall_factorsThrough_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/2b212e9a-ca6d-5746-9fbf-9077313038ae
-- title:
--   Clopen locus where the extra level is L₀·(m/ℓ)P
-- statement:
--   Fix primes $q,q'$ and rationals $a,b$ such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds, i.e. $a>0$ or $b>0$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the algebra $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ has all its nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule which is an order and is maximal among the orders containing it, let $N,m\in\mathbb N$, let $\ell$ be a prime with $\ell\mid m$, and let $L_0\subseteq\Lambda$ be a $\mathbb Z$-submodule with $\ell x\in L_0$ for every $x\in\Lambda$. Let $S$ be a commutative ring in which the image of $m$ is a unit, let $E$ be a fake elliptic curve over $S$ of level $N$ with $\Lambda$-action in the sense of `FakeEllipticCurve`, let $P$ be a full level-$m$ structure on $E$, and let $K$ be an extra level structure at $\ell$, with closed immersion $K.\mathrm{levK}:K\to E.A$. Then there is an open subscheme $V$ of $\operatorname{Spec} S$ whose underlying set is closed and which has the following property: for every algebraically closed field $k$ and every ring homomorphism $s_k:S\to k$, the image of $\operatorname{Spec}(s_k):\operatorname{Spec} k\to\operatorname{Spec} S$ lies in $V$ if and only if, for every $Q:\operatorname{Spec} k\to E.A$ over $\operatorname{Spec}(s_k)$, the morphism $Q$ factors through $K.\mathrm{levK}$ precisely when $Q$ equals $E.\mathrm{act}(x)\circ\bigl((m/\ell)\cdot P_{s_k}\bigr)$ for some $x\in\Lambda$ lying in $L_0$, where $P_{s_k}$ is the base change of the section $P$ along $s_k$, $(m/\ell)$ denotes natural-number division, and the multiple is taken for the relative group law $E.L$.
--
--   This identifies the locus in $\operatorname{Spec} S$ on which a given extra level structure at $\ell$ coincides with the $\ell$-torsion subgroup cut out by $L_0$ acting on the canonical $\ell$-torsion point $(m/\ell)P$ of the full level-$m$ structure, and asserts that this locus is open and closed. It is used in the construction of the moduli problem for fake elliptic curves with full level-$m$ and extra level-$\ell$ structure, being cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_flat_surjective_withFullLevel_forall_factorsThrough_iff`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_flat_surjective_withFullLevel_forall_factorsThrough_iff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_isClosed_range_subset_iff_forall_factorsThrough_iff.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
open AlgebraicGeometry

theorem CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_isClosed_range_subset_iff_forall_factorsThrough_iff
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} (m ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    {S : Type} [CommRing S] (hm : IsUnit ((m : ℕ) : S)) (E : FakeEllipticCurve Λ N S) (P : E.FullLevel m)
    (K : E.ExtraLevel ℓ) :
    ∃ V : (Spec (CommRingCat.of S)).Opens, IsClosed (V : Set ↥(Spec (CommRingCat.of S))) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k),
        Set.range (geomPoint k sk) ⊆ (V : Set ↥(Spec (CommRingCat.of S))) ↔
          ∀ Q : SchemeHomOver (geomPoint k sk) E.f,
            FactorsThrough K.levK Q ↔
              ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
                pushPt (E.act x) (E.act_over x)
                  (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) = Q := by sorry
