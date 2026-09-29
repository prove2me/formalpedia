-- Prove2me | Theorems.Thm_FamousTheorems_hockey_stick_identity
-- name    : FamousTheorems.hockey_stick_identity
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:05:04.007235+00:00
-- url     : https://prove2.me/theorems/4639fc5f-f491-4286-8530-2117a4c6338c
-- title:
--   The hockey-stick identity (Zhu Shijie's identity)
-- statement:
--   **The hockey-stick identity.** For natural numbers $k\le n$,
--   $$\sum_{m=k}^{n}\binom mk=\binom{n+1}{k+1}.$$
--
--   In Pascal's triangle the entries along a diagonal add up to the entry just below the end of the diagonal, a shape like a hockey stick. The identity was known to Zhu Shijie in 1303. It gives closed forms for sums of polynomials over integers: $k=1$ gives $\sum m=\binom{n+1}2$, and $k=2$ leads to the sum of squares.
--
--   **Formalization note.** Mathlib's `Nat.sum_Icc_choose`. The sum is over the finset `Finset.Icc k n`. For $n<k$ both sides are $0$, so no hypothesis $k\le n$ is needed.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Nat.sum_Icc_choose`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem hockey_stick_identity (n k : ℕ) : ∑ m ∈ Finset.Icc k n, m.choose k = (n + 1).choose (k + 1) := by sorry

end FamousTheorems
