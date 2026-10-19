-- Prove2me | Theorems.Thm_DynFairDiv_Uniform_ffaTotal_uniform_monotone
-- name    : DynFairDiv.Uniform.ffaTotal_uniform_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:54.580038+00:00
-- url     : https://prove2.me/theorems/a418283c-6911-4798-ade2-d9664e7d99b7
-- title:
--   p. 959, proof of Theorem 4 — the total S^t allocated by FFA on the infinite d-uniform vector increases with t
-- statement:
--   Fix $d \ge 1$ and $\sigma \ge 0$, and let $S^t$ be the total resource allocated by the frugally fair algorithm with ratio $\sigma$ on the infinite $d$-uniform control vector when $t$ users are present ($S^0 = 0$). Then $S^t$ is nondecreasing in $t$:
--   $$S^0 \le S^1 \le S^2 \le \cdots .$$
--
--   Monotonicity means the worst over-allocation of FFA on a $d$-uniform vector happens in the limit, so the supremum of $S^t$ equals its limit.
--
--   **Formalization Note.** The hypothesis $\sigma \ge 0$ is added (for $\sigma < 0$ the totals decrease; the paper uses fairness ratios, which are nonnegative). Only the monotonicity conclusion is stated; the printed increment $S^{t'} - S^t$ on p. 959 omits a factor $\ell$ in its numerator (the correct value is $\sigma\ell(d-i)/((\ell d+i)(\ell d+i+1)(\ell d+i+\ell+1))$), which does not affect its sign.
-- source:
--   Vardi, Psomas, Friedman, Dynamic Fair Resource Division, Math. Oper. Res. 47(2):945–968 (2022), p. 959, proof of Theorem 4, 'We first show that S^t increases with t'

import Mathlib
import Definitions.Def_DynFairDiv_Uniform_Model

namespace DynFairDiv.Uniform

theorem ffaTotal_uniform_monotone (d : ℕ) (hd : 1 ≤ d) (σ : ℝ) (hσ : 0 ≤ σ) :
    Monotone (ffaTotal (uniformCV d) σ) := by sorry

end DynFairDiv.Uniform
