-- Prove2me | Theorems.Thm_DQI_Imperfect_eq_179
-- name    : DQI.Imperfect.eq_179
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:04:05.794972+00:00
-- url     : https://prove2.me/theorems/23a3af49-5e1d-4307-9d0c-cfd7ae8a22bf
-- title:
--   Equation (179) — normalized objective equality
-- statement:
--   Let $\widetilde P_D(f)$ be the unnormalized state of correctly decoded errors, and suppose its squared norm $N=\sum_{k=0}^{\ell}w_k^2(1-\varepsilon_k)$ is positive. The objective expectation after the Hadamard transform and normalization is
--
--   $$
--   \langle f\rangle=\frac{w^\top\bar A^{(m,\ell,D)}w}{N}.
--   $$
--
--   This equality identifies the normalized quantity averaged over the random sign vector in Theorem 10.1.
--
--   **Formalization Note** The displayed equation (179) also prints an inequality comparing this fraction to a denominator $w^\top w$. That inequality is false when the numerator is negative, so this item states the equality only. The explicit conditions $N>0$ and $\ell\le m$ keep normalization well defined.
-- source:
--   Jordan et al., Optimization by Decoded Quantum Interferometry, arXiv:2408.08292v5, p. 41, (179), first equality

import Mathlib
import Definitions.Def_DQI_Imperfect_Setting

namespace DQI.Imperfect

theorem eq_179 (m n ℓ : ℕ) (hℓ : ℓ ≤ m)
    (B : Matrix (Fin m) (Fin n) (ZMod 2)) (v : Fin m → ZMod 2) (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (w : Fin (ℓ + 1) → ℝ)
    (hN : 0 < (∑ k, (w k) ^ 2 * (1 - epsk B dec k.val))) :
    expObj B v (hadamard (PtD B v dec ℓ w)) =
      (w ⬝ᵥ (AbarD B v dec ℓ).mulVec w) /
        (∑ k, (w k) ^ 2 * (1 - epsk B dec k.val)) := by sorry

end DQI.Imperfect
