-- Prove2me | Theorems.Thm_BallPolyApprox_VertexBudget_proposition_17
-- name    : BallPolyApprox.VertexBudget.proposition_17
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:55:25.287193+00:00
-- url     : https://prove2.me/theorems/b27a9809-febc-45de-acc4-1f9bb0193893
-- title:
--   Proposition 17 — $\mathbb E\Delta_d(R_{d,M}^{-1}P)\le C_1(1-t_0)/(t_0\sqrt d)$ (41) and the upper bound (42)
-- statement:
--   There exist absolute constants $C_0,C_1,d_0>0$ such that for all $d\ge d_0$ and all $M$ ($M\ge2d$, the standing assumption of §5.3.1) whose associated mode $t_0$ satisfies $t_0\ge C_0/\sqrt d$,
--   $$\mathbb E\Delta_d(R_{d,M}^{-1}P)\le C_1\frac{1-t_0}{t_0\sqrt d}\quad(41).$$
--   Consequently, for $d\ge d_0$ and every $0<\varepsilon\le\varepsilon_0$,
--   $$\log N_\varepsilon(d)\le Cd\log\Big(1+\frac1{\varepsilon\sqrt d}\Big)\quad(42),$$
--   that is, some polytope $\operatorname{conv}V$ with $\log|V|\le Cd\log(1+1/(\varepsilon\sqrt d))$ has $\Delta_d\le\varepsilon$.
--
--   Differences from the source:
--   - encoding: §5.3.1 standing assumption M ≥ 2d → hypothesis 2d ≤ M in (41); reason: the subsection's standing assumption; t_0 is defined only for these M
--   - reading: (42) uses ε_0 and C without introducing them → ∃ ε_0 ∈ (0, 1), ∃ C > 0; reason: read existentially, as in Theorem 1
--   - encoding: log N_ε(d) ≤ X → ∃ finite V with Δ_d(conv V) ≤ ε and log|V| ≤ X; reason: N_ε(d) is the least such |V|; the existence form avoids sInf ∅ = 0
--   - encoding: E Δ_d(R^{−1}_{d,M}P) in ℝ → lower Lebesgue integral in [0, ∞] bounded by ENNReal.ofReal; reason: the integrand is nonnegative
-- source:
--   Gorodzha, Hoehner, Kur, Approximating the Euclidean Ball by Polytopes, arXiv:2610.34651 (sha256 164dc885…), Proposition 17, p. 17 (PDF 19)

import Mathlib
import Definitions.Def_RGGDetect_unifSphere
import Definitions.Def_BallPolyApprox_VertexBudget_VolumeError
import Definitions.Def_BallPolyApprox_VertexBudget_RandomPolytope

set_option autoImplicit false

open MeasureTheory

namespace BallPolyApprox.VertexBudget

/-- Proposition 17 (p. 17, PDF 19), under the standing assumption `M ≥ 2d` of §5.3.1: there are
absolute constants `C_0, C_1, d_0 > 0` such that for all `d ≥ d_0` and all `M` whose mode `t_0`
satisfies `t_0 ≥ C_0/√d`, `E Δ_d(R_{d,M}^{−1} P) ≤ C_1 (1 − t_0)/(t_0 √d)` (41). Consequently, for
some `ε_0 ∈ (0, 1)` and `C > 0`, for `d ≥ d_0` and every `0 < ε ≤ ε_0`,
`log N_ε(d) ≤ C d log(1 + 1/(ε√d))` (42), i.e. some polytope with at most
`exp(C d log(1 + 1/(ε√d)))` vertices has `Δ_d ≤ ε`. -/
theorem proposition_17 :
    ∃ C0 C1 : ℝ, 0 < C0 ∧ 0 < C1 ∧ ∃ d0 : ℕ, 0 < d0 ∧
      (∀ d : ℕ, d0 ≤ d → ∀ M : ℕ, 2 * d ≤ M → C0 / Real.sqrt d ≤ modeT0 d M →
        expErrScaled d M ≤
          ENNReal.ofReal (C1 * (1 - modeT0 d M) / (modeT0 d M * Real.sqrt d))) ∧
      ∃ ε0 C : ℝ, 0 < ε0 ∧ ε0 < 1 ∧ 0 < C ∧
        ∀ d : ℕ, d0 ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ ε0 →
          ∃ V : Finset (Rd d), ballErr (polytope V) ≤ ε ∧
            Real.log V.card ≤ C * d * Real.log (1 + 1 / (ε * Real.sqrt d)) := by sorry

end BallPolyApprox.VertexBudget
