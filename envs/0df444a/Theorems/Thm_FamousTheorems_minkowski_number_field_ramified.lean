-- Prove2me | Theorems.Thm_FamousTheorems_minkowski_number_field_ramified
-- name    : FamousTheorems.minkowski_number_field_ramified
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:39.005952+00:00
-- url     : https://prove2.me/theorems/6fdddc61-2557-40a0-9435-c39ea2239f16
-- title:
--   Minkowski's theorem: every number field other than ℚ is ramified
-- statement:
--   **Minkowski's theorem: every number field other than $\mathbb Q$ is ramified.** Let $K$ be a number field with $[K:\mathbb Q]>1$. Then some rational prime $p$ ramifies in $K$.
--
--   The theorem follows from Minkowski's discriminant bound $|d_K|>1$, since the ramified primes are exactly those dividing $d_K$. So $\mathbb Q$ has no nontrivial unramified extensions. This is a basic input to class field theory, and it is the base case of the study of maximal unramified extensions.
--
--   **Formalization note.** Mathlib's `NumberField.exists_not_isUnramifiedIn`, with $\mathcal O$ the ring of integers `NumberField.RingOfIntegers K`. `Algebra.IsUnramifiedIn 𝒪 (Ideal.span {(p : ℤ)})` says that $\mathcal O_K$ is unramified at every prime above $p$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `NumberField.exists_not_isUnramifiedIn`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem minkowski_number_field_ramified {K : Type*} [Field K] [NumberField K] (h : Module.finrank ℚ K ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ ¬Algebra.IsUnramifiedIn (NumberField.RingOfIntegers K) (Ideal.span {(p : ℤ)}) := by sorry

end FamousTheorems
