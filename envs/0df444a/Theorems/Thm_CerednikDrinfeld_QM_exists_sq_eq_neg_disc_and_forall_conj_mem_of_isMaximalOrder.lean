-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_sq_eq_neg_disc_and_forall_conj_mem_of_isMaximalOrder
-- name    : CerednikDrinfeld.QM.exists_sq_eq_neg_disc_and_forall_conj_mem_of_isMaximalOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/667f6e40-1237-537f-b455-c46c6a9379e8
-- title:
--   Maximal orders contain μ with μ²=-qq' normalising conjugation
-- statement:
--   Let $q$ and $q'$ be primes with $q' \neq q$, and let $a, b \in \mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q}, a, b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, that is: $0 < a$ or $0 < b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$, the base change $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all its nonzero elements invertible precisely when $q \in v$ or $q' \in v$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is a maximal order, i.e. $\Lambda$ contains $1$, is closed under multiplication, spans $\mathbb{H}[\mathbb{Q},a,b]$ over $\mathbb{Q}$ and is finitely generated, and every such order containing $\Lambda$ equals $\Lambda$. The conclusion is a conjunction. First, there exists $\mu \in \Lambda$ with $\mu^2 = -(qq') \cdot 1$, the scalar being the rational number $q q'$. Second, for every $\mu \in \Lambda$ satisfying $\mu^2 = -(qq')\cdot 1$ and every $x \in \Lambda$, there exists $y \in \Lambda$ with $\mu y = \bar{x} \mu$, where $\bar{\;\cdot\;}$ denotes quaternionic conjugation (`star`). Thus the second clause asserts the inclusion $\bar{\Lambda} \mu \subseteq \mu \Lambda$ for any such $\mu$, without any uniqueness assertion for $y$.
--
--   The element $\mu$ is the standard generator of the two-sided ideal of reduced norm equal to the discriminant $qq'$ of an indefinite quaternion algebra ramified exactly at $q$ and $q'$; together with quaternionic conjugation it supplies the positive involution $x \mapsto \mu^{-1}\bar{x}\mu$ of $\Lambda$, stated here in the division-free form $\mu y = \bar{x}\mu$. It is used in the construction and rigidification of the fake elliptic curves attached to $\Lambda$ in the Čerednik–Drinfeld part of the development, in particular by the results on rigidified pairs and on formal modules of height four.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_sq_eq_neg_disc_and_forall_conj_mem_of_isMaximalOrder.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion

open QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.exists_sq_eq_neg_disc_and_forall_conj_mem_of_isMaximalOrder
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) :
    (∃ μ : ↥Λ, (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b]))) ∧
    (∀ μ : ↥Λ, (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])) →
      ∀ x : ↥Λ, ∃ y : ↥Λ, (μ : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) = star (x : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b])) := by sorry
