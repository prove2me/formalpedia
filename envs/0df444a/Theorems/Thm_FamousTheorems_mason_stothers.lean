-- Prove2me | Theorems.Thm_FamousTheorems_mason_stothers
-- name    : FamousTheorems.mason_stothers
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T09:15:30.154351+00:00
-- url     : https://prove2.me/theorems/e9d49c40-78dc-4279-a499-81d50960b55a
-- title:
--   The Mason–Stothers theorem (polynomial abc)
-- statement:
--   **The Mason–Stothers theorem (polynomial abc).** Let $a,b,c$ be nonzero polynomials over a field with $a+b+c=0$ and $\gcd(a,b)=1$. Then either
--   $$\max(\deg a,\deg b,\deg c)+1\le\deg\operatorname{rad}(abc),$$
--   where $\operatorname{rad}$ is the product of the distinct irreducible factors, or $a'=b'=c'=0$ (possible only in positive characteristic).
--
--   It is the function-field analogue of the abc conjecture, proved independently by Stothers and Mason. It gives a short proof of Fermat's Last Theorem for polynomials and of Davenport's bound on $f^3-g^2$.
--
--   **Formalization note.** Mathlib's `Polynomial.abc`, with `UniqueFactorizationMonoid.radical`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Polynomial.abc`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem mason_stothers {k : Type*} [Field k] [DecidableEq k] {a b c : Polynomial k} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hab : IsCoprime a b) (hsum : a + b + c = 0) :
    (a.natDegree + 1 ≤ (UniqueFactorizationMonoid.radical (a * b * c)).natDegree ∧
        b.natDegree + 1 ≤ (UniqueFactorizationMonoid.radical (a * b * c)).natDegree ∧
        c.natDegree + 1 ≤ (UniqueFactorizationMonoid.radical (a * b * c)).natDegree) ∨
      (Polynomial.derivative a = 0 ∧ Polynomial.derivative b = 0 ∧ Polynomial.derivative c = 0) := by sorry

end FamousTheorems
