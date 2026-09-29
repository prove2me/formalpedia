-- Prove2me | Theorems.Thm_FamousTheorems_cyclotomic_ring_of_integers_7b
-- name    : FamousTheorems.cyclotomic_ring_of_integers_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:33:00.147586+00:00
-- url     : https://prove2.me/theorems/c218b027-253b-4d6a-8a9c-1607705c496e
-- title:
--   The ring of integers of a cyclotomic field is ℤ[ζ]
-- statement:
--   **The ring of integers of a cyclotomic field is $\mathbb Z[\zeta]$.** Let $n\ge1$, let $K=\mathbb Q(\zeta_n)$ be the $n$-th cyclotomic field and let $\zeta\in K$ be a primitive $n$-th root of unity. Then the ring of integers of $K$ is $\mathbb Z[\zeta]$.
--
--   It follows that the powers $1,\zeta,\dots,\zeta^{\varphi(n)-1}$ form an integral basis of $K$. This is the basic structural result about cyclotomic fields. Kummer's work on Fermat's Last Theorem and much of Iwasawa theory rely on it. The proof first treats prime powers, using that $1-\zeta$ generates a totally ramified prime, and then combines coprime conductors using the discriminants.
--
--   **Formalization note.** Mathlib's `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton`. `IsIntegralClosure (Algebra.adjoin ℤ {ζ}) ℤ K` says that the subring $\mathbb Z[\zeta]$ of $K$ is exactly the set of elements of $K$ integral over $\mathbb Z$. `IsCyclotomicExtension {n} ℚ K` says that $K$ is generated over $\mathbb Q$ by a primitive $n$-th root of unity.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cyclotomic_ring_of_integers_7b {n : ℕ} [NeZero n] {K : Type*} [Field K] [CharZero K] [IsCyclotomicExtension {n} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) : IsIntegralClosure (Algebra.adjoin ℤ ({ζ} : Set K)) ℤ K := by sorry

end FamousTheorems
