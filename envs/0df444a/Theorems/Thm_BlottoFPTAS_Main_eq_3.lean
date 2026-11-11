-- Prove2me | Theorems.Thm_BlottoFPTAS_Main_eq_3
-- name    : BlottoFPTAS.Main.eq_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:40:41.10625+00:00
-- url     : https://prove2.me/theorems/3beec2dc-9703-4aa5-b10b-d51f2f3cfbaa
-- title:
--   §2, Eq. (3) — Reg_A + Reg_B = U(μ_B; 1) + U(μ_A; b) − 1, so U(μ_B; 1) + U(μ_A; b) ≤ 1 + ε gives an ε-Nash equilibrium
-- statement:
--   Let $n\ge1$, values $v_i>0$ with $\sum_iv_i=1$, a budget ratio $b\in(0,1]$, and strategies $\mu_A$ on $X(1)$ and $\mu_B$ on $X(b)$. Since the game is constant-sum, adding the regret definitions gives
--   $$\mathrm{Reg}_A(\mu_A,\mu_B)+\mathrm{Reg}_B(\mu_A,\mu_B)=U(\mu_B;1)+U(\mu_A;b)-1,$$
--   and, each regret being nonnegative, $U(\mu_B;1)+U(\mu_A;b)\le1+\varepsilon$ implies that $(\mu_A,\mu_B)$ is an $\varepsilon$-Nash equilibrium. This identity reduces equilibrium computation to two separate minimizations of the opponent's supremum payoff, and is used in every error estimate of §5.
--
--   Differences from the source:
--   - encoding: mixed strategy = probability distribution on the pure strategy space → Borel probability measure on Fin n → ℝ with full mass on X(c); reason: Lean convention; same strategies
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), p. 5, §2, Eq. (3)

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_Game

open MeasureTheory

namespace BlottoFPTAS.Main

/-- **§2, Eq. (3)** (Bichler, Ghosh, arXiv:2611.05221, held version sha256 cac3638e…, p. 5).
For values `v_i > 0` summing to one, a budget ratio `b ∈ (0, 1]` and strategies `μ_A` on `X(1)`,
`μ_B` on `X(b)`: `Reg_A + Reg_B = U(μ_B; 1) + U(μ_A; b) − 1`, and
`U(μ_B; 1) + U(μ_A; b) ≤ 1 + ε` implies that `(μ_A, μ_B)` is an `ε`-Nash equilibrium. -/
theorem eq_3 {n : ℕ} (hn : 1 ≤ n) (v : Fin n → ℝ) (hv : ∀ i, 0 < v i) (hsum : ∑ i, v i = 1)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b ≤ 1) (μA μB : Measure (Fin n → ℝ))
    (hA : IsStrategy n 1 μA) (hB : IsStrategy n b μB) :
    regA v μA μB + regB v b μA μB = U v μB 1 + U v μA b - 1 ∧
      ∀ ε : ℝ, U v μB 1 + U v μA b ≤ 1 + ε → IsEpsNash v b ε μA μB := by sorry

end BlottoFPTAS.Main
