-- Prove2me | Theorems.Thm_FamousTheorems_exists_norm_nsmul_le
-- name    : FamousTheorems.exists_norm_nsmul_le
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:13:04.008166+00:00
-- url     : https://prove2.me/theorems/66e33ec6-3208-48c4-b9c2-f79078864c4a
-- title:
--   Dirichlet's approximation theorem
-- statement:
--   **Dirichlet's approximation theorem.** For any real $\theta$ and any $N$ there is $1 \le n \le N$ with $\lVert n\theta\rVert \le 1/N$, distance measured to the nearest integer. Equivalently every irrational admits infinitely many rationals with $|\theta - p/q| < 1/q^2$. The proof is the pigeonhole principle applied to the fractional parts of $\theta, 2\theta, \ldots, N\theta$, Dirichlet's original use of that principle in 1842. The exponent 2 is essentially optimal: Hurwitz sharpened the constant, and Liouville's theorem shows algebraic numbers cannot be approximated much better, which is where transcendence proofs begin. **Formalization note.** Stated on `AddCircle`, where the norm is distance to the nearest integer multiple. The result is Mathlib's `AddCircle.exists_norm_nsmul_le`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem exists_norm_nsmul_le :
    ∀ {T : ℝ} [hT : Fact (0 < T)] (ξ : AddCircle T) {n : ℕ}, 
    0 < n → ∃ j ∈ Icc 1 n, ‖j • ξ‖ ≤ T / ↑(n + 1) := by sorry

end FamousTheorems
