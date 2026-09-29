-- Prove2me | Theorems.Thm_DeBruijnNewman_Ht_upper_bound
-- name    : DeBruijnNewman.Ht_upper_bound
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T13:16:18.777648+00:00
-- url     : https://prove2.me/theorems/12642cca-c51d-4b20-a2ac-14f95883e4c9
-- title:
--   Lemma 4 - upper bound for $H_t$ just below the real axis
-- statement:
--   Estimate (7) of Lemma 4. Fix $C \ge 0$. There is a constant $A > 0$, depending only on $C$, such that for every time $t$ with $\Lambda < t \le 0$, every $x \ge 0$ and every $\kappa$ with $0 \le \kappa \le C$, the value of $H_t$ at the point $z = x - i\kappa\log_+ x$ obeys
--   $$|H_t(x - i\kappa\log_+ x)| \le \exp\!\left(-\frac{\pi x}{8} + A\,(\log_+ x)^2\right).$$
--   Here $\log_+ x = \log(2 + |x|)$. The source writes this as $H_t(z) \ll \exp(-\pi x/8 + O_C(\log_+^2 x))$; since $(\log_+ x)^2 \ge (\log 2)^2 > 0$, an implied multiplicative constant can be absorbed into $A$. The hypothesis $\Lambda < t \le 0$ is the standing assumption of the paper and is only satisfiable when $\Lambda < 0$.
-- source:
--   B. Rodgers and T. Tao, "The de Bruijn-Newman constant is non-negative", Forum of Mathematics, Pi 8 (2020), e6, https://doi.org/10.1017/fmp.2020.6, Lemma 4, equation (7), p. 8

import Mathlib
import Definitions.Def_DeBruijnNewman_core
import Definitions.Def_DeBruijnNewman_zeros

namespace DeBruijnNewman

theorem Ht_upper_bound (C : ℝ) (hC : 0 ≤ C) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, Lambda < t → t ≤ 0 → ∀ x κ : ℝ, 0 ≤ x → 0 ≤ κ → κ ≤ C →
      ‖H t ((x : ℂ) - Complex.I * ((κ * logPlus x : ℝ) : ℂ))‖
        ≤ Real.exp (-(Real.pi * x) / 8 + A * (logPlus x) ^ 2) := by sorry

end DeBruijnNewman
