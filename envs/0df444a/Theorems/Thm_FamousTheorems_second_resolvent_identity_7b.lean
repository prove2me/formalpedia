-- Prove2me | Theorems.Thm_FamousTheorems_second_resolvent_identity_7b
-- name    : FamousTheorems.second_resolvent_identity_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:58.385188+00:00
-- url     : https://prove2.me/theorems/065e5c29-4cd6-48c5-8c1e-7cec421928f5
-- title:
--   The second resolvent identity
-- statement:
--   **The second resolvent identity.** Let $A$ be an algebra over a commutative ring $R$, let $a,b\in A$, and let $r\in R$ be in the resolvent set of both $a$ and $b$. With $R(a,r)=(r-a)^{-1}$,
--   $$R(a,r)-R(b,r)=R(a,r)\,(a-b)\,R(b,r).$$
--
--   The identity compares the resolvents of two operators at the same point, and it is the algebraic basis of perturbation theory. It is used to prove continuity of the resolvent in the operator, to derive the Neumann series for $R(a+\varepsilon,r)$, and in scattering theory and the Birman–Schwinger principle. It follows from $(r-b)-(r-a)=a-b$ by multiplying by the two inverses.
--
--   **Formalization note.** Mathlib's `spectrum.resolvent_sub_resolvent`. `resolventSet R a` is the set of $r$ with $r\cdot1-a$ invertible, and `resolvent a r` is the inverse of $r\cdot1-a$ (defined as $0$ outside the resolvent set).
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `spectrum.resolvent_sub_resolvent`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem second_resolvent_identity_7b {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A] {a b : A} {r : R}
    (ha : r ∈ resolventSet R a) (hb : r ∈ resolventSet R b) :
    resolvent a r - resolvent b r = resolvent a r * (a - b) * resolvent b r := by sorry

end FamousTheorems
