-- Prove2me | Theorems.Thm_DeBruijnNewman_lower_bound_on_gaps
-- name    : DeBruijnNewman.lower_bound_on_gaps
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T13:37:06.226998+00:00
-- url     : https://prove2.me/theorems/cdc93837-9676-42bf-8f8e-c70fe699bc93
-- title:
--   Proposition 13 - lower bound on the gaps between zeros
-- statement:
--   Proposition 13, under the standing assumption $\Lambda < 0$ of the source. There is an absolute constant $A > 0$ such that for every time $t$ with $\Lambda/2 \le t \le 0$, every enumeration $(x_j)$ of the zeros of $H_t$ and all distinct nonzero indices $j, k$,
--   $$\log \frac{1}{|x_j - x_k|} \le A\,(\log_+ j)^2 \log_+ \log_+ j .$$
--   In the notation of the source this is the bound $\max_{k \ne j} H_{jk}(t) \ll (\log_+^2 j)\log_+\log_+ j$ on the Hamiltonian interaction, equation (59): no zero is exponentially close to another one, with a bound that is uniform in $t$ and grows only poly-logarithmically in $j$.
-- source:
--   B. Rodgers and T. Tao, "The de Bruijn-Newman constant is non-negative", Forum of Mathematics, Pi 8 (2020), e6, https://doi.org/10.1017/fmp.2020.6, Proposition 13, equation (59), p. 34

import Mathlib
import Definitions.Def_DeBruijnNewman_core
import Definitions.Def_DeBruijnNewman_zeros
import Definitions.Def_DeBruijnNewman_energy

namespace DeBruijnNewman

theorem lower_bound_on_gaps (hLambda : Lambda < 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, Lambda / 2 ≤ t → t ≤ 0 → ∀ x : ℤ → ℝ, IsZeroEnumeration t x →
      ∀ j k : ℤ, j ≠ 0 → k ≠ 0 → k ≠ j →
        Hint x j k ≤ A * logPlus (j : ℝ) ^ 2 * logPlus (logPlus (j : ℝ)) := by sorry

end DeBruijnNewman
