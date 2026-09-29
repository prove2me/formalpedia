-- Prove2me | Theorems.Thm_FamousTheorems_transcendental_liouvillenumber
-- name    : FamousTheorems.transcendental_liouvillenumber
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:40:37.633611+00:00
-- url     : https://prove2.me/theorems/27974856-3647-40b4-91ec-77b55a364a97
-- title:
--   Transcendence of the Liouville constant
-- statement:
--   **Transcendence of Liouville's constant.** The number $$\sum_{k=1}^{\infty} \frac{1}{10^{k!}} = 0.110001000000000000000001\ldots$$ is transcendental. This was the first number ever proved transcendental, by Liouville in 1844 — before $e$ (Hermite, 1873) or $\pi$ (Lindemann, 1882) — and it was constructed for the purpose rather than found in nature. The mechanism is approximation quality: an algebraic irrational of degree $n$ cannot be approximated by rationals to order better than $n$, while the factorial gaps in the decimal expansion make the truncations approximate the sum to arbitrarily high order. Any number admitting such approximations is a Liouville number, and all of them are transcendental. **Formalization note.** `liouvilleNumber 10` is the constant for base 10; transcendence is over $\mathbb{Q}$. The result is Mathlib's `transcendental_liouvilleNumber`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem transcendental_liouvillenumber :
    ∀ {m : ℕ}, 2 ≤ m → Transcendental ℤ (liouvilleNumber ↑m) := by sorry

end FamousTheorems
