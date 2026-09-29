-- Prove2me | Theorems.Thm_FamousTheorems_cyclotomic_field_discriminant_7b
-- name    : FamousTheorems.cyclotomic_field_discriminant_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:33:05.517488+00:00
-- url     : https://prove2.me/theorems/327d3392-be69-4443-ae5f-1546ebe616c4
-- title:
--   The discriminant of the n-th cyclotomic field
-- statement:
--   **The discriminant of the $n$-th cyclotomic field.** Let $n\ge1$ and $K=\mathbb Q(\zeta_n)$. Then
--   $$d_K=(-1)^{\varphi(n)/2}\,\frac{n^{\varphi(n)}}{\prod_{p\mid n}p^{\varphi(n)/(p-1)}},$$
--   where $\varphi$ is Euler's totient function and the product runs over the primes dividing $n$.
--
--   The formula shows which primes ramify in $\mathbb Q(\zeta_n)$: exactly the primes dividing $n$, apart from $2$ when $n\equiv2\pmod4$. It is used to compute rings of integers and class numbers of cyclotomic fields and, through the conductor–discriminant formula, of their subfields.
--
--   **Formalization note.** Mathlib's `IsCyclotomicExtension.Rat.discr`. `NumberField.discr K` is the absolute discriminant of $K$ as an integer. The division is integer division, and it is exact here. For $n=1,2$ the formula gives $1$, the discriminant of $\mathbb Q$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsCyclotomicExtension.Rat.discr`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cyclotomic_field_discriminant_7b (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K] :
    NumberField.discr K = (-1) ^ (n.totient / 2) *
      ((n : ℤ) ^ n.totient / ((∏ p ∈ n.primeFactors, p ^ (n.totient / (p - 1)) : ℕ) : ℤ)) := by sorry

end FamousTheorems
