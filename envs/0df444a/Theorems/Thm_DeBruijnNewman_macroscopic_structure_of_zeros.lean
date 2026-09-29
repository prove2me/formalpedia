-- Prove2me | Theorems.Thm_DeBruijnNewman_macroscopic_structure_of_zeros
-- name    : DeBruijnNewman.macroscopic_structure_of_zeros
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T13:21:44.153998+00:00
-- url     : https://prove2.me/theorems/a53f0225-a3b0-495d-aec3-5ee03c0765c4
-- title:
--   Corollary 10 - macroscopic structure of the zeros of $H_t$
-- statement:
--   Corollary 10, equations (50) and (52), for times $\Lambda < t \le 0$, for every enumeration $(x_j)$ of the zeros of $H_t$ and every family $(\xi_j)$ of classical locations.
--
--   **Position of the zeros, equation (50).** There is an absolute constant $A > 0$ with
--   $$|x_j - \xi_j| \le A \log_+ \xi_j \qquad \text{for all nonzero } j .$$
--
--   **Local spacing, equation (52).** For every $\varepsilon > 0$ there is an index $J$ such that whenever $j \ge J$ is positive and $j < k \le j + (\log_+ \xi_j)^2$,
--   $$\left| x_k - x_j - \frac{4\pi (k-j)}{\log_+ \xi_j} \right| \le \varepsilon \log_+ \xi_j .$$
--   Informally: on scales between $o(\log_+\xi_j)$ and $o(\xi_j)$ the zeros look like an arithmetic progression of spacing $4\pi/\log_+\xi_j$.
-- source:
--   B. Rodgers and T. Tao, "The de Bruijn-Newman constant is non-negative", Forum of Mathematics, Pi 8 (2020), e6, https://doi.org/10.1017/fmp.2020.6, Corollary 10, equations (50) and (52), p. 23

import Mathlib
import Definitions.Def_DeBruijnNewman_core
import Definitions.Def_DeBruijnNewman_zeros

namespace DeBruijnNewman

theorem macroscopic_structure_of_zeros :
    (∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, Lambda < t → t ≤ 0 → ∀ x xi : ℤ → ℝ,
        IsZeroEnumeration t x → IsClassicalLocations xi →
        ∀ j : ℤ, j ≠ 0 → |x j - xi j| ≤ A * logPlus (xi j)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ J : ℤ, ∀ t : ℝ, Lambda < t → t ≤ 0 → ∀ x xi : ℤ → ℝ,
        IsZeroEnumeration t x → IsClassicalLocations xi →
        ∀ j k : ℤ, 0 < j → J ≤ j → j < k → (k : ℝ) ≤ (j : ℝ) + logPlus (xi j) ^ 2 →
          |x k - x j - 4 * Real.pi * ((k : ℝ) - (j : ℝ)) / logPlus (xi j)|
            ≤ ε * logPlus (xi j)) := by sorry

end DeBruijnNewman
