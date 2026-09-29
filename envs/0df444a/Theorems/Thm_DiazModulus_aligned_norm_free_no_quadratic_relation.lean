-- Prove2me | Theorems.Thm_DiazModulus_aligned_norm_free_no_quadratic_relation
-- name    : DiazModulus.aligned_norm_free_no_quadratic_relation
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:34:51.660166+00:00
-- url     : https://prove2.me/theorems/89563704-a141-48b3-9ff2-513418daa2dc
-- title:
--   In the aligned, norm-free case, u, ū and 2πi satisfy no rational quadratic relation
-- statement:
--   Let $u = x + iy$ with $x \neq 0$, let $r \in \mathbb{Q}$, and put $\beta = \pi(y + r\pi)$. Suppose that $\beta \neq 0$, that $\beta$ and $|u|^{2}$ are algebraic, and that $|u|^{2} \notin \mathbb{Q}\beta$. Then $u$, $\bar u$ and $2\pi i$ satisfy no non-trivial rational quadratic relation: if
--
--   $$\sum_{k,l} F_{kl}\, e_k e_l = 0, \qquad e = (u, \bar u, 2\pi i),\ F_{kl} \in \mathbb{Q},$$
--
--   then $F_{kl} + F_{lk} = 0$ for all $k, l$.
--
--   These are the hypotheses of `DiazModulus.aligned_norm_free_no_rational_log_matrix`, without the transcendence of $\pi$, which that node assumes and which is now taken from `DiazModulus.pi_transcendental`. With `DiazModulus.four_exp_barrier_of_no_quadratic_relation` it gives that node.
-- source:
--   Formal proof: Diaz modulus mission, 25 September 2026 (C. Perassi); extracted from the proof of DiazModulus.aligned_norm_free_no_rational_log_matrix.

import Mathlib

open ComplexConjugate

namespace DiazModulus

theorem aligned_norm_free_no_quadratic_relation (u : ℂ) (r : ℚ) (hre : u.re ≠ 0)
    (hβ0 : Real.pi * (u.im + (r : ℝ) * Real.pi) ≠ 0)
    (hβ : IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ))
    (hρ : IsAlgebraic ℚ ((((‖u‖ : ℝ)) ^ 2 : ℝ) : ℂ))
    (hfree : ¬ ∃ c : ℚ, (‖u‖ : ℝ) ^ 2 = (c : ℝ) * (Real.pi * (u.im + (r : ℝ) * Real.pi)))
    (F : Fin 3 → Fin 3 → ℚ)
    (h : ∑ k, ∑ l, (F k l : ℂ) *
      (![u, conj u, 2 * ((Real.pi : ℝ) : ℂ) * Complex.I] k *
        ![u, conj u, 2 * ((Real.pi : ℝ) : ℂ) * Complex.I] l) = 0) :
    ∀ k l, F k l + F l k = 0 := by
  sorry

end DiazModulus
