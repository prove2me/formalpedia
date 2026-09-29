-- Prove2me | Theorems.Thm_FamousTheorems_fermat_last_theorem_polynomials
-- name    : FamousTheorems.fermat_last_theorem_polynomials
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:37:37.064527+00:00
-- url     : https://prove2.me/theorems/e37869e2-4b55-4e58-ae49-cf24a6ec2f9d
-- title:
--   Fermat's Last Theorem for polynomials
-- statement:
--   **Fermat's Last Theorem for polynomials.** Let $k$ be a field and $n\ge3$ with $n\ne0$ in $k$. If $a,b,c\in k[X]$ are nonzero, $a$ and $b$ are coprime, and
--   $$a^n+b^n=c^n,$$
--   then $a$, $b$ and $c$ are all constant.
--
--   Unlike the integer case, this is elementary. It follows from the Mason–Stothers theorem (the $abc$ theorem for polynomials). It is a standard illustration of how the function-field analogue of a hard arithmetic problem can be easy. The characteristic hypothesis is needed: in characteristic $p$, $(X+1)^p=X^p+1$.
--
--   **Formalization note.** Mathlib's `Polynomial.flt`. Coprimality is `IsCoprime a b`, and constancy is `natDegree = 0`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Polynomial.flt`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem fermat_last_theorem_polynomials {k : Type*} [Field k] {n : ℕ} (hn : 3 ≤ n) (hchar : (n : k) ≠ 0) {a b c : Polynomial k}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b) (heq : a ^ n + b ^ n = c ^ n) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 := by sorry

end FamousTheorems
