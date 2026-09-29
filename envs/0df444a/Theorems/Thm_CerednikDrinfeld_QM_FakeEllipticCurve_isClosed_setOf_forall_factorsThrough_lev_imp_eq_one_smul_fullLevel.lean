-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isClosed_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isClosed_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/abb5a2a3-eb8b-5f87-9cff-47ce205cf493
-- title:
--   Closedness of the L₀·(m/ℓ)P trivial-intersection locus
-- statement:
--   Let $q,q'$ be primes and $a,b\in\mathbb{Q}$, and suppose that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: $0<a$ or $0<b$, and for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ that is a maximal order (it contains $1$, is closed under multiplication, spans the algebra over $\mathbb{Q}$, is finitely generated, and is maximal among such orders), let $N,m\in\mathbb{N}$, let $\ell$ be a prime dividing $m$, and let $L_0\subseteq\Lambda$ be a $\mathbb{Z}$-submodule with $\ell\cdot\Lambda\subseteq L_0$, stable under left multiplication by $\Lambda$, and of relative index $\ell^2$ in $\Lambda$ as additive groups. Let $S$ be a commutative ring in which the images of $m$ and of $N$ are units, let $E$ be a `FakeEllipticCurve Λ N S` — an $S$-scheme $f:A\to\operatorname{Spec}S$ with a commutative relative group law $L$, smooth proper with connected fibres of dimension $2$, carrying a $\Lambda$-action `act` compatible with $f$, additive and multiplicative in the stated sense and with the prescribed trace behaviour on tangent spaces, together with a level structure $\mathrm{lev}:C\to A$ — and let $P$ be a full level-$m$ structure on $E$ (a section $P$ over $\operatorname{Spec}S$ killed by $m$, whose geometric translates under $\Lambda$ exhaust the $m$-torsion, with annihilator $m\Lambda$). Then the set of primes $p\subseteq S$ such that for every algebraically closed field $k$ and every ring homomorphism $sk:S\to k$ with kernel $p$, and every $x\in\Lambda$ lying in $L_0$, the point $\mathrm{act}(x)$ applied to $(m/\ell)$ times the geometric fibre of $P$ at $sk$ factors through $\mathrm{lev}$ (i.e. admits a lift $\operatorname{Spec}k\to C$ composing with $\mathrm{lev}$ to it) only if it equals the identity section over $\operatorname{Spec}k$, is closed in $\operatorname{Spec}S$.
--
--   This is the closedness half of the statement that the locus in the base where the $\Lambda$-line $L_0\cdot(m/\ell)P$ meets the level-$N$ structure only in the identity is both open and closed, used in the construction of the Čerednik–Drinfeld moduli description of Shimura curves attached to an indefinite quaternion algebra ramified exactly at $q$ and $q'$. It feeds the variant for integral domains, [`CerednikDrinfeld.QM.FakeEllipticCurve.forall_factorsThrough_lev_imp_eq_one_smul_fullLevel_of_isDomain`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.forall_factorsThrough_lev_imp_eq_one_smul_fullLevel_of_isDomain).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isClosed_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isClosed_setOf_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} (m ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (hL₀_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀)
    (hL₀_index : L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2)
    {S : Type} [CommRing S] (hm : IsUnit ((m : ℕ) : S)) (E : FakeEllipticCurve Λ N S) (P : E.FullLevel m)
    (hN : IsUnit ((N : ℕ) : S)) :
    IsClosed {p : PrimeSpectrum S |
      ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k), RingHom.ker sk = p.asIdeal →
        ∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
          FactorsThrough E.lev
            (pushPt (E.act x) (E.act_over x)
              (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk))) →
          pushPt (E.act x) (E.act_over x)
              (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) = E.L.one (geomPoint k sk)} := by sorry
