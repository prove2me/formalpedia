-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuliT_isIntegral_of_isAlgClosed_of_not_dvd_of_squarefree_of_ne
-- name    : CerednikDrinfeld.QM.IsCoarseModuliT.isIntegral_of_isAlgClosed_of_not_dvd_of_squarefree_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/cf633d1b-6b83-53a2-bd83-f3bc760e73a2
-- title:
--   Integrality of coarse moduli of pairs with extra ℓ-level
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ that is an order maximal among the orders containing it, let $N \neq 0$ be squarefree with $q \nmid N$ and $q' \nmid N$, and let $\ell$ be a prime distinct from $q$ and $q'$. Let $k$ be an algebraically closed field of characteristic zero, $X$ a scheme, $\pi_X : X \to \operatorname{Spec} k$ a morphism, and `pt` a rule assigning, to every commutative ring $S$, every $s : \operatorname{Spec} S \to \operatorname{Spec} k$ and every pair consisting of a fake elliptic curve over $S$ for $\Lambda$ with level-$N$ datum together with an extra level structure at $\ell$ (a closed subscheme of the total space, containing the identity, stable under the group law, inversion and the $\Lambda$-action, killed by $\ell$, meeting the level-$N$ subscheme only in the identity, finite flat of finite presentation of fibre rank $\ell^2$ with geometric fibres isomorphic to $(\mathbb{Z}/\ell)^2$), a morphism $\operatorname{Spec} S \to X$ over $s$. Assume `IsCoarseModuliT Λ N ℓ X πX pt`: `pt` is constant on isomorphism classes, compatible with base change along ring homomorphisms taking pullback pairs to pullbacks, surjective and injective on points with values in algebraically closed fields, and universal among such point rules over $\operatorname{Spec} k$. Assume further that $\pi_X$ is separated and locally of finite type. Then $X$ is integral.
--
--   This is the geometric statement that a coarse moduli scheme over an algebraically closed field of characteristic zero, for pairs consisting of a fake elliptic curve with level-$N$ datum and an extra $\ell$-level structure, is an integral scheme; classically it reflects the connectedness of the corresponding Shimura curve with level structure, obtained from strong approximation. It is the input used by the assembly [`CerednikDrinfeld.QM.exists_isCoarseModuli_integral_of_isUnit_six_of_not_dvd_of_squarefree_of_isUnit_two_of_isUnit_three_of_ne`](thm.html#CerednikDrinfeld.QM.exists_isCoarseModuli_integral_of_isUnit_six_of_not_dvd_of_squarefree_of_isUnit_two_of_isUnit_three_of_ne), which produces integral coarse moduli schemes over more general bases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCoarseModuliT_isIntegral_of_isAlgClosed_of_not_dvd_of_squarefree_of_ne.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
open AlgebraicGeometry

theorem CerednikDrinfeld.QM.IsCoarseModuliT.isIntegral_of_isAlgClosed_of_not_dvd_of_squarefree_of_ne
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q) {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hN : Squarefree N) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of k))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of k)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πX)
    (hX : IsCoarseModuliT Λ N ℓ X πX pt) (hsep : IsSeparated πX) (hlft : LocallyOfFiniteType πX) :
    IsIntegral X := by sorry
