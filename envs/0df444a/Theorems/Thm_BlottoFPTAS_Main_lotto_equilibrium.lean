-- Prove2me | Theorems.Thm_BlottoFPTAS_Main_lotto_equilibrium
-- name    : BlottoFPTAS.Main.lotto_equilibrium
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:40:53.650975+00:00
-- url     : https://prove2.me/theorems/f2137741-8f58-43b1-a459-8118a204bd0d
-- title:
--   §4.1.1 — feasible strategies with the General Lotto marginals (6) form an exact Nash equilibrium with payoffs 1 − b/2 and b/2
-- statement:
--   Let $v_i>0$ with $\sum_iv_i=1$, $b\in(0,1]$, and let $\mu_A$, $\mu_B$ be strategies on $X(1)$ and $X(b)$ whose marginals are the Lotto marginals (6),
--   $$X_i\sim\mathrm{Unif}[0,\ell_i],\qquad Y_i\sim(1-b)\delta_0+b\,\mathrm{Unif}[0,\ell_i],\qquad\ell_i=2v_i.$$
--   Then every deviation $y\in X(b)$ earns at most $b/2$ against $\mu_A$, every deviation $x\in X(1)$ earns at most $1-b/2$ against $\mu_B$, $(\mu_A,\mu_B)$ is an exact Nash equilibrium, and the expected payoffs are $1-b/2$ for $A$ and $b/2$ for $B$. Appendix F.3 uses this for equal budgets.
--
--   Differences from the source:
--   - encoding: any pair of feasible couplings of (6) → strategies on X(1), X(b) whose coordinate marginals (pushforwards) equal Unif[0, 2v_i], resp. (1 − b)δ₀ + b Unif[0, 2v_i]; reason: Lean convention; same objects
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), p. 14, §4.1.1

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_Game
import Definitions.Def_BlottoFPTAS_Main_Lotto

open MeasureTheory

namespace BlottoFPTAS.Main

/-- **§4.1.1, Lotto marginals give an exact equilibrium** (Bichler, Ghosh, arXiv:2611.05221, held
version sha256 cac3638e…, p. 14). For values `v_i > 0` summing to one and `b ∈ (0, 1]`, let
`μ_A`, `μ_B` be strategies on `X(1)` and `X(b)` whose marginals are the Lotto marginals (6),
`X_i ∼ Unif[0, ℓ_i]` and `Y_i ∼ (1 − b)δ₀ + b Unif[0, ℓ_i]` with `ℓ_i = 2v_i`. Then every
deviation of B earns at most `b/2` against `μ_A`, every deviation of A earns at most `1 − b/2`
against `μ_B`, `(μ_A, μ_B)` is an exact Nash equilibrium, and the expected payoffs are
`1 − b/2` for A and `b/2` for B. -/
theorem lotto_equilibrium {n : ℕ} (hn : 1 ≤ n) (v : Fin n → ℝ) (hv : ∀ i, 0 < v i)
    (hsum : ∑ i, v i = 1) (b : ℝ) (hb0 : 0 < b) (hb1 : b ≤ 1) (μA μB : Measure (Fin n → ℝ))
    (hA : IsStrategy n 1 μA) (hB : IsStrategy n b μB)
    (hmargA : ∀ i, marginal μA i = unifOn (2 * v i))
    (hmargB : ∀ i, marginal μB i = atomUnif b (2 * v i)) :
    U v μA b ≤ b / 2 ∧ U v μB 1 ≤ 1 - b / 2 ∧ IsEpsNash v b 0 μA μB ∧
      expUA v μA μB = 1 - b / 2 ∧ expUB v μA μB = b / 2 := by sorry

end BlottoFPTAS.Main
