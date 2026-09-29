-- Prove2me | Theorems.Thm_DeligneSerre_exists_factorization_charZero_quotient
-- name    : DeligneSerre.exists_factorization_charZero_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/571970b8-baca-5362-a975-02d3d541ba3c
-- title:
--   Deligne–Serre lifting: characteristic-zero factorisation of a character
-- statement:
--   Let $T$ be a commutative ring which is finite as a $\mathbb{Z}$-module and torsion-free as a $\mathbb{Z}$-module, let $k$ be a field, and let $\chi : T \to k$ be a ring homomorphism. The assertion is that there is an ideal $\mathfrak{p}$ belonging to `minimalPrimes T`, i.e. a minimal element among the prime ideals of $T$, such that all of the following hold: $\mathfrak{p} \subseteq \ker \chi$; for every integer $n$, if the image of $n$ under the structure map $\mathbb{Z} \to T$ lies in $\mathfrak{p}$ then $n = 0$; the quotient ring $T/\mathfrak{p}$ has characteristic zero; $T/\mathfrak{p}$ is a domain; $T/\mathfrak{p}$ is finite as a $\mathbb{Z}$-module; $T/\mathfrak{p}$ is integral over $\mathbb{Z}$ as a $\mathbb{Z}$-algebra; and there exists a ring homomorphism $\mathrm{red} : T/\mathfrak{p} \to k$ whose composite with the quotient map $T \to T/\mathfrak{p}$ equals $\chi$. Thus $\chi$ factors through a quotient of $T$ which is an order-like domain of characteristic zero, module-finite over $\mathbb{Z}$.
--
--   This is the algebraic content of the Deligne–Serre lifting lemma (Lemme 6.11 of "Formes modulaires de poids 1"): a character of a $\mathbb{Z}$-finite, $\mathbb{Z}$-torsion-free Hecke-type algebra with values in a field (possibly of positive characteristic) factors through a characteristic-zero domain which is module-finite over $\mathbb{Z}$. It is used in the construction of a characteristic-zero normalised eigenform from a maximal ideal of the Hecke algebra, via [`CuspForm.exists_isNormalizedEigenform_ker_of_isMaximal`](thm.html#CuspForm.exists_isNormalizedEigenform_ker_of_isMaximal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DeligneSerre_exists_factorization_charZero_quotient.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem DeligneSerre.exists_factorization_charZero_quotient {T : Type*} [CommRing T] [Module.Finite ℤ T]
  [Module.IsTorsionFree ℤ T] {k : Type*} [Field k] (χ : T →+* k) :
  ∃ 𝔭 ∈ minimalPrimes T,
    𝔭 ≤ RingHom.ker χ ∧
      (∀ (n : ℤ), (algebraMap ℤ T) n ∈ 𝔭 → n = 0) ∧
        CharZero (T ⧸ 𝔭) ∧
          IsDomain (T ⧸ 𝔭) ∧
            Module.Finite ℤ (T ⧸ 𝔭) ∧ Algebra.IsIntegral ℤ (T ⧸ 𝔭) ∧ ∃ red : T ⧸ 𝔭 →+* k, red.comp (Ideal.Quotient.mk 𝔭) = χ := by sorry
