-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuli_isIntegral_of_isAlgClosed_of_not_dvd_of_squarefree
-- name    : CerednikDrinfeld.QM.IsCoarseModuli.isIntegral_of_isAlgClosed_of_not_dvd_of_squarefree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/2d3cbfe6-918b-55a4-a3d9-e682064efa53
-- title:
--   Integrality of the quaternionic coarse moduli scheme over k
-- statement:
--   Let $q\neq q'$ be primes and let $a,b\in\mathbb{Q}$ be such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds, i.e. $a>0$ or $b>0$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all its nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order, that is, an order (containing $1$, multiplicatively closed, $\mathbb{Q}$-spanning the algebra, finitely generated) that is maximal among orders containing it. Let $N$ be a nonzero natural number with $q\nmid N$, $q'\nmid N$ and $N$ squarefree, and let $k$ be an algebraically closed field of characteristic zero. Let $X$ be a scheme with a morphism $\pi_X : X\to\operatorname{Spec} k$, and let $\mathrm{pt}$ assign, to every commutative ring $S$, every morphism $s:\operatorname{Spec} S\to\operatorname{Spec} k$ and every fake elliptic curve over $S$ with $\Lambda$-action and level-$N$ data in the sense of `FakeEllipticCurve Λ N S` (a commutative relative group law on a smooth proper morphism with connected fibres of dimension $2$, an action of $\Lambda$ whose induced endomorphisms satisfy the reduced-trace condition, together with the level structures), a morphism $\operatorname{Spec} S\to X$ over $s$. Assume `IsCoarseModuli Λ N X πX pt`: $\mathrm{pt}$ is constant on isomorphism classes, compatible with base change along ring homomorphisms and the corresponding pullbacks of fake elliptic curves, surjective and injective up to isomorphism on points with values in algebraically closed fields, and universal among all such pointed schemes over $\operatorname{Spec} k$. Assume further that $\pi_X$ is separated and locally of finite type. Then $X$ is integral.
--
--   This is the statement that the coarse moduli scheme of fake elliptic curves with $\Lambda$-action and $\Gamma_0(N)$-type level structure, formed over an algebraically closed field of characteristic zero, is an integral scheme — the irreducibility and reducedness of the quaternionic Shimura curve in characteristic zero. It is the form in which integrality enters the assembly [`CerednikDrinfeld.QM.exists_isCoarseModuli_integral_of_isUnit_six_of_not_dvd_of_squarefree_of_isUnit_two_of_isUnit_three_of_ne`](thm.html#CerednikDrinfeld.QM.exists_isCoarseModuli_integral_of_isUnit_six_of_not_dvd_of_squarefree_of_isUnit_two_of_isUnit_three_of_ne), applied at a geometric point of its base; the hypotheses $q\nmid N$, $q'\nmid N$ exclude the cases in which the moduli problem is empty.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCoarseModuli_isIntegral_of_isAlgClosed_of_not_dvd_of_squarefree.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
open AlgebraicGeometry

theorem CerednikDrinfeld.QM.IsCoarseModuli.isIntegral_of_isAlgClosed_of_not_dvd_of_squarefree
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q) {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hN : Squarefree N)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of k))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of k)), FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (hX : IsCoarseModuli Λ N X πX pt) (hsep : IsSeparated πX) (hlft : LocallyOfFiniteType πX) :
    IsIntegral X := by sorry
