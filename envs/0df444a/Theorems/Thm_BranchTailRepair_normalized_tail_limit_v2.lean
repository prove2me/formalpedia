-- Prove2me | Theorems.Thm_BranchTailRepair_normalized_tail_limit_v2
-- name    : BranchTailRepair.normalized_tail_limit_v2
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T16:17:47.40765+00:00
-- url     : https://prove2.me/theorems/a7b05605-8a61-4ce7-85e9-9c53bfcf89f8
-- title:
--   Uniform vanishing of a normalized discrete logarithmic tail
-- statement:
--   Let kₙ ≥ 2 be integers and let ℓₙ, Lₙ, Mₙ, hₙ be real sequences such that ℓₙ ≤ 1, Lₙ ≥ 1, Mₙ ≥ 1, and 0 < hₙ ≤ 1. Assume Mₙ → +∞. Then
--   \[
--   \frac{h_n}{L_n}\sum_{j=0}^{\infty}\frac{L_n+\log(M_n+jh_n+3)}{\left(1+\frac{(M_n+jh_n)^2-\ell_n/4}{k_n}\right)^{k_n}}\longrightarrow 0.
--   \]
--   The series is absolutely convergent, and its normalized value lies between 0 and 96/Mₙ². This is a uniform tail estimate for varying powers and mesh sizes. It makes no assertion about the zeros of the Riemann zeta function.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Repair of the discrete high-tail comparison in On the Infinitude of Off-Critical Zeros, §4.4.4. Complete self-contained Lean development, 2026-11-16.

import Mathlib

theorem BranchTailRepair.normalized_tail_limit_v2 (k : ℕ → ℕ) (hk : ∀ n, 2≤k n)
    (l L M h : ℕ → ℝ) (hl : ∀ n, l n≤1) (hL : ∀ n, 1≤L n)
    (hM : ∀ n, 1≤M n) (hh : ∀ n, 0<h n) (hh1 : ∀ n, h n≤1)
    (hMt : Filter.Tendsto M Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n => h n/L n * (∑' j : ℕ, (L n+Real.log (M n+(j : ℝ)*h n+3))*
      ((1+((M n+(j : ℝ)*h n)^2-l n/4)/(k n : ℝ))^(k n))⁻¹)) Filter.atTop (nhds 0) := by sorry
