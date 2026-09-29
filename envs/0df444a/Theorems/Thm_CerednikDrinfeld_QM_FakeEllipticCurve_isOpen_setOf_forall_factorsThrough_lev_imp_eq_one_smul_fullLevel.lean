-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isOpen_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isOpen_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/94bdc549-6392-5c6e-97ac-c42e368654fc
-- title:
--   Openness of the transversality locus of a full level structure
-- statement:
--   Let $q,q'$ be primes and $a,b\in\mathbb{Q}$ be such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds, i.e. $a>0$ or $b>0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order (an order, maximal among orders containing it), let $N,m\in\mathbb{N}$, let $\ell$ be a prime dividing $m$, and let $L_0\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule with $L_0\subseteq\Lambda$, with $\ell x\in L_0$ for all $x\in\Lambda$, stable under left multiplication by elements of $\Lambda$, and of relative index $\ell^2$ in $\Lambda$ as additive subgroups. Let $S$ be a commutative ring in which the image of $m$ is a unit, let $E$ be a fake elliptic curve of level $N$ over $S$ for $\Lambda$ (an $S$-scheme $E.f : E.A \to \operatorname{Spec} S$ with commutative relative group law $E.L$, the abelian-scheme property bundle, two-dimensional fibres, a $\Lambda$-action by $S$-endomorphisms $E.act$ satisfying the additivity, multiplicativity and trace axioms, together with its level datum $E.lev : E.C \to E.A$), and let $P$ be a full level-$m$ structure on $E$, so $P.P$ is a section of $E.f$ killed by $m$ whose geometric translates exhaust the $m$-torsion and whose annihilator in $\Lambda$ is $m\Lambda$. Then the set of $\mathfrak{p}\in\operatorname{Spec} S$ with the following property is open: for every algebraically closed field $k$ and ring homomorphism $s_k : S \to k$ with kernel $\mathfrak{p}$, and every $x\in\Lambda$ with $x\in L_0$, if the point $E.act(x)$ applied to the $(m/\ell)$-fold multiple (for $E.L$, natural-number division $m/\ell$) of the pullback of $P.P$ along the geometric point $\operatorname{Spec} k \to \operatorname{Spec} S$ determined by $s_k$ factors through $E.lev$, i.e. its underlying morphism is $P_0$ followed by $E.lev$ for some $P_0 : \operatorname{Spec} k \to E.C$, then that point equals the identity section of $E.L$ at this geometric point.
--
--   This is the openness in the base of the transversality (or disjointness) locus: the locus of primes over whose geometric points the $\ell$-line $L_0\cdot\frac{m}{\ell}P$ of translates of the full level-$m$ structure meets the level subscheme $E.C$ only in the origin. It is used to pass from this condition at one point to a condition over a neighbourhood, and is cited in the form `forall_factorsThrough_lev_imp_eq_one_smul_fullLevel_of_isDomain`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isOpen_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isOpen_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} (m ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (hL₀_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀)
    (hL₀_index : L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2)
    {S : Type} [CommRing S] (hm : IsUnit ((m : ℕ) : S)) (E : FakeEllipticCurve Λ N S) (P : E.FullLevel m) :
    IsOpen {p : PrimeSpectrum S |
      ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k), RingHom.ker sk = p.asIdeal →
        ∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
          FactorsThrough E.lev
            (pushPt (E.act x) (E.act_over x)
              (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk))) →
          pushPt (E.act x) (E.act_over x)
              (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) = E.L.one (geomPoint k sk)} := by sorry
