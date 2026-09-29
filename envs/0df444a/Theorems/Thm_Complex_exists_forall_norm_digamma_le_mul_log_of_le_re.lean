-- Prove2me | Theorems.Thm_Complex_exists_forall_norm_digamma_le_mul_log_of_le_re
-- name    : Complex.exists_forall_norm_digamma_le_mul_log_of_le_re
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/f802fe38-547d-59f2-847d-b30aee89b472
-- title:
--   Logarithmic growth of digamma in a vertical strip
-- statement:
--   For every real $\delta$ with $0 < \delta$ there exists a real constant $C$ with $0 < C$ such that for all complex $s$ satisfying $\delta \le \operatorname{Re} s$ and $\operatorname{Re} s \le 2$ one has $\lVert \psi(s) \rVert \le C \cdot \log(2 + \lvert \operatorname{Im} s \rvert)$, where $\psi =$ `Complex.digamma` is the complex digamma function, $\lVert \cdot \rVert$ is the complex absolute value, $\lvert \operatorname{Im} s \rvert$ is the real absolute value of the imaginary part, and $\log$ is the real logarithm. Thus the digamma function grows at most logarithmically in the imaginary direction, uniformly on the closed vertical strip $\delta \le \operatorname{Re} s \le 2$; the constant $C$ is allowed to depend on $\delta$, and no claim of uniformity as $\delta \to 0$ is made. Note that the bounding function $\log(2+\lvert \operatorname{Im} s\rvert)$ is bounded below by $\log 2 > 0$, so the bound is non-trivial at every point of the strip.
--
--   This is the standard logarithmic bound on $\Gamma'/\Gamma$ in a vertical strip of bounded positive real part, obtained from the partial-fraction series $\psi(s) + \gamma = \sum_{k \ge 0}\bigl(1/(k+1) - 1/(k+s)\bigr)$ valid for $\operatorname{Re} s > 0$. It forms the first conjunct of a combined estimate that also bounds the logarithmic derivatives of the archimedean Gamma factors, used in the analytic estimates for $L$-functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_exists_forall_norm_digamma_le_mul_log_of_le_re.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Complex.exists_forall_norm_digamma_le_mul_log_of_le_re
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, δ ≤ s.re → s.re ≤ 2 →
      ‖Complex.digamma s‖ ≤ C * Real.log (2 + |s.im|) := by sorry
