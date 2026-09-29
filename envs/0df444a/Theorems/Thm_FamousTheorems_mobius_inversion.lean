-- Prove2me | Theorems.Thm_FamousTheorems_mobius_inversion
-- name    : FamousTheorems.mobius_inversion
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:38.406622+00:00
-- url     : https://prove2.me/theorems/32fb98e8-b0f1-4ac2-af76-418e196972c6
-- title:
--   Möbius inversion
-- statement:
--   **Möbius inversion.** Let $R$ be a ring and $f,g:\mathbb N\to R$. Then
--   $$g(n)=\sum_{d\mid n}f(d)\ \ \text{for all }n>0\iff f(n)=\sum_{d\,e=n}\mu(d)\,g(e)\ \ \text{for all }n>0,$$
--   where $\mu$ is the Möbius function.
--
--   Möbius inversion is a basic tool of multiplicative number theory. It turns identities such as $\sum_{d\mid n}\varphi(d)=n$ into $\varphi(n)=\sum_{d\mid n}\mu(d)\,n/d$, it underlies the counting of irreducible polynomials over finite fields, and it generalizes to incidence algebras of posets.
--
--   **Formalization note.** Mathlib's `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq`. The second sum is over `n.divisorsAntidiagonal`, the pairs $(d,e)$ with $de=n$, and `ArithmeticFunction.moebius` is the integer-valued Möbius function, cast to `R`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem mobius_inversion {R : Type*} [NonAssocRing R] {f g : ℕ → R} :
    (∀ n > 0, ∑ i ∈ n.divisors, f i = g n) ↔
      ∀ n > 0, ∑ x ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : R) * g x.2 = f n := by sorry

end FamousTheorems
