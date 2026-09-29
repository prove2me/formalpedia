-- Prove2me | Theorems.Thm_DeBruijnNewman_riemann_von_mangoldt_type_formulae
-- name    : DeBruijnNewman.riemann_von_mangoldt_type_formulae
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T13:17:17.370146+00:00
-- url     : https://prove2.me/theorems/b9d36005-0969-456d-9cb5-2f7f55283dd0
-- title:
--   Theorem 9 - Riemann-von Mangoldt type formulae for the zeros of $H_t$
-- statement:
--   Theorem 9, both parts, for times $\Lambda < t \le 0$.
--
--   **Global count, equation (48).** There is an absolute constant $A > 0$ such that for every such $t$ and every $T > 0$,
--   $$\bigl|N_t([0,T]) - \Psi(T)\bigr| \le A\,(\log_+ T)^2,$$
--   where $N_t([0,T])$ is the number of zeros of $H_t$ in $[0,T]$ and $\Psi(T) = \frac{T}{4\pi}\log\frac{T}{4\pi} - \frac{T}{4\pi}$.
--
--   **Short interval count, equation (49).** For every $C > 0$ and every $\varepsilon > 0$ there is $T_0 > 0$ such that for every $t$ with $\Lambda < t \le 0$, every $T \ge T_0$ and every $\alpha \in [0, C]$,
--   $$\left|N_t\bigl([T,\,T + \alpha\log_+ T]\bigr) - \frac{\alpha(\log_+ T)^2}{4\pi}\right| \le \varepsilon (\log_+ T)^2 .$$
--   The threshold $T_0$ is allowed to depend on $C$ and $\varepsilon$ but not on $\alpha$ or $t$, matching the uniformity stated in the source.
-- source:
--   B. Rodgers and T. Tao, "The de Bruijn-Newman constant is non-negative", Forum of Mathematics, Pi 8 (2020), e6, https://doi.org/10.1017/fmp.2020.6, Theorem 9, equations (48)-(49), p. 23

import Mathlib
import Definitions.Def_DeBruijnNewman_core
import Definitions.Def_DeBruijnNewman_zeros

namespace DeBruijnNewman

theorem riemann_von_mangoldt_type_formulae :
    (∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, Lambda < t → t ≤ 0 → ∀ T : ℝ, 0 < T →
        |(zeroCount t (Set.Icc 0 T) : ℝ) - Psi T| ≤ A * (logPlus T) ^ 2) ∧
    (∀ C : ℝ, 0 < C → ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, 0 < T₀ ∧
      ∀ t : ℝ, Lambda < t → t ≤ 0 → ∀ T : ℝ, T₀ ≤ T → ∀ α : ℝ, 0 ≤ α → α ≤ C →
        |(zeroCount t (Set.Icc T (T + α * logPlus T)) : ℝ)
            - α * (logPlus T) ^ 2 / (4 * Real.pi)| ≤ ε * (logPlus T) ^ 2) := by sorry

end DeBruijnNewman
