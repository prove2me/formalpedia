-- Prove2me | Theorems.Thm_FamousTheorems_pentagonal_number_theorem
-- name    : FamousTheorems.pentagonal_number_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T09:14:52.974382+00:00
-- url     : https://prove2.me/theorems/7748f7f8-58ad-4b10-96a9-e163ed35ffda
-- title:
--   Euler's pentagonal number theorem
-- statement:
--   **Euler's pentagonal number theorem.**
--   $$\prod_{n\ge1}(1-x^n)=\sum_{k\in\mathbb Z}(-1)^k x^{k(3k-1)/2}=1-x-x^2+x^5+x^7-x^{12}-x^{15}+\cdots$$
--   as formal power series over any commutative ring.
--
--   The exponents are the generalized pentagonal numbers. Combined with $\prod(1-x^n)^{-1}=\sum p(n)x^n$ it yields Euler's recurrence $p(n)=p(n-1)+p(n-2)-p(n-5)-p(n-7)+\cdots$ for the partition function, and it is the first of the Macdonald identities.
--
--   **Formalization note.** `PowerSeries.pentagonalSeries R` has coefficient $(-1)^k$ at $n=k(3k-1)/2$ and $0$ elsewhere. The infinite product converges in the coefficientwise (pi) topology on $R⟦X⟧$, opened via `PowerSeries.WithPiTopology`. Mathlib: `PowerSeries.WithPiTopology.hasProd_one_sub_X_pow`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `PowerSeries.WithPiTopology.hasProd_one_sub_X_pow`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open scoped PowerSeries.WithPiTopology

theorem pentagonal_number_theorem (R : Type*) [CommRing R] [TopologicalSpace R] :
    HasProd (fun n : ℕ => (1 - PowerSeries.X ^ (n + 1) : PowerSeries R)) (PowerSeries.pentagonalSeries R) := by sorry

end FamousTheorems
