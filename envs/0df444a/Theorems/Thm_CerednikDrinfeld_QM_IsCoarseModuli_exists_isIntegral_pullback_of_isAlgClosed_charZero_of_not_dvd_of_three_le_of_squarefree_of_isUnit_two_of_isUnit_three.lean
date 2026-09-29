-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuli_exists_isIntegral_pullback_of_isAlgClosed_charZero_of_not_dvd_of_three_le_of_squarefree_of_isUnit_two_of_isUnit_three
-- name    : CerednikDrinfeld.QM.IsCoarseModuli.exists_isIntegral_pullback_of_isAlgClosed_charZero_of_not_dvd_of_three_le_of_squarefree_of_isUnit_two_of_isUnit_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/7b020270-726a-5189-917c-af61d9150ec7
-- title:
--   An integral characteristic-zero geometric fibre of a coarse Shimura model
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that $\mathbb H[\mathbb Q,a,b]$ is indefinite ($0 < a$ or $0 < b$) and, for every height-one prime $v$ of the ring of integers of $\mathbb Q$, the completion $\mathbb H[\mathbb Q,a,b] \otimes_{\mathbb Q} \mathbb Q_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb Z$-submodule which is an order (containing $1$, closed under multiplication, $\mathbb Q$-spanning, finitely generated) and is maximal among orders containing it. Let $N \geq 1$ be squarefree with $q \nmid N$, $q' \nmid N$, and let $M \geq 1$ be such that $N$, an integer $m_0 \geq 3$, as well as $2$ and $3$, are units in $\mathbb Z[1/M] =$ `Localization.Away ((M : ℕ) : ℤ)`. Let $\pi_X : X \to \operatorname{Spec} \mathbb Z[1/M]$ be a scheme over $\mathbb Z[1/M]$ together with point-maps $\mathrm{pt}$ assigning to each ring $S$, each $S$-point $s$ of the base and each fake elliptic curve with $\Lambda$-action and level-$N$ data over $S$ a morphism to $X$ over $s$, such that `IsCoarseModuli` holds: $\mathrm{pt}$ is invariant under isomorphism of fake elliptic curves, compatible with pullback along ring maps over the base, bijective on isomorphism classes over algebraically closed fields, and universal among such point-maps. Assume $\pi_X$ separated, quasi-compact, locally of finite type, flat, proper and smooth of relative dimension one. Then there exist an algebraically closed field $C$ of characteristic zero and a morphism $s_C : \operatorname{Spec} C \to \operatorname{Spec} \mathbb Z[1/M]$ for which the pullback of $\pi_X$ along $s_C$ is an integral scheme.
--
--   This provides the one characteristic-zero integral geometric fibre required as input to the integrality transfer for the Shimura curve attached to an indefinite quaternion algebra ramified exactly at $q,q'$ with Eichler level $N$. It is used in establishing integrality of such coarse models over algebraically closed bases and in the construction of the coarse moduli scheme for squarefree level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCoarseModuli_exists_isIntegral_pullback_of_isAlgClosed_charZero_of_not_dvd_of_three_le_of_squarefree_of_isUnit_two_of_isUnit_three.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsCoarseModuli.exists_isIntegral_pullback_of_isAlgClosed_charZero_of_not_dvd_of_three_le_of_squarefree_of_isUnit_two_of_isUnit_three
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q) {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hN : Squarefree N) (M : ℕ) [NeZero M]
    (hN : IsUnit ((N : ℕ) : Localization.Away ((M : ℕ) : ℤ)))
    (m₀ : ℕ) (hm₀ : 3 ≤ m₀) (hm₀u : IsUnit ((m₀ : ℕ) : Localization.Away ((M : ℕ) : ℤ)))
    (h2 : IsUnit ((2 : ℕ) : Localization.Away ((M : ℕ) : ℤ))) (h3 : IsUnit ((3 : ℕ) : Localization.Away ((M : ℕ) : ℤ)))
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (hX : IsCoarseModuli Λ N X πX pt) (hsep : IsSeparated πX) (hqc : QuasiCompact πX) (hlft : LocallyOfFiniteType πX)
    (hflat : Flat πX) (hproper : IsProper πX) (hsmooth : SmoothOfRelativeDimension 1 πX) :
    ∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : CharZero C)
      (sC : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ)))),
      IsIntegral (Limits.pullback πX sC) := by sorry
