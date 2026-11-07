-- Prove2me | Theorems.Thm_EffHorizonProphet_exists_calibrated_rule
-- name    : EffHorizonProphet.exists_calibrated_rule
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:44:02.851855+00:00
-- url     : https://prove2.me/theorems/a81a7614-1ffe-46a2-89c3-fc45dadf7bc3
-- title:
--   Remark 5 and Remark 16 — generalized quantile and exact acceptance probability
-- statement:
--   Let $D$ be an admissible law, possibly with atoms, and let $b\ge1$ be real. There are $\alpha\ge0$ and a rule with threshold $\alpha$ such that
--   $$P(Y>\alpha)\le\frac1b\le P(Y\ge\alpha),$$
--   with tie-breaking probability $\theta=\dfrac{1/b-P(Y>\alpha)}{P(Y=\alpha)}$ when $P(Y=\alpha)>0$, and whose acceptance probability is exactly $1/b$.
--
--   Applied with $b=B$, this makes the policy of Theorem 6 well defined on every admissible law.
--
--   Differences from the source:
--   - generalization: the target is $a/n$, that is $b=B$ → any real $b\ge1$; reason: $B$ is one value of $b$
--   - encoding: $\alpha_s$ and $X_i$ in the scale of phase $s$ → $\alpha$ and $Y$ in the base scale; reason: for $\tilde\gamma>0$ the same inequalities and the same $\theta$
--   - reading: $\tau$ is a stopping time for the filtration of $(X_i)$ (p.3), while Remarks 5 and 16 add randomized tie-breaking with coins $U_i$ → the coins are coordinates of the sample space and $\tau$ is a stopping time for $(Y_i,U_i)$; reason: Remark 16 introduces the coins this way, and the proof on p.21 uses them to reach every acceptance probability $p$
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Remark 5, p.9; Remark 16, p.31

import Mathlib
import Definitions.Def_EffHorizonProphet_IsAdmissible
import Definitions.Def_EffHorizonProphet_acceptProb

open MeasureTheory

namespace EffHorizonProphet

/-- **Remark 5 and Remark 16** (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), p.9 and p.31): for an admissible law, possibly with atoms, and
a target `1/b ∈ (0, 1]` there is a generalized quantile `α ≥ 0` with
`P(Y > α) ≤ 1/b ≤ P(Y ≥ α)` and, with `θ = (1/b - P(Y > α)) / P(Y = α)` when `P(Y = α) > 0`, a
rule whose acceptance probability is exactly `1/b`.

**Formalization Note** The printed remarks take `b = n/a = B`, in the scale of `X_i`. For `γ̃ > 0`
the inequalities and `θ` are the same in the base scale. -/
theorem exists_calibrated_rule (D : Measure ℝ) (hD : IsAdmissible D) (b : ℝ) (hb : 1 ≤ b) :
    ∃ α : ℝ, 0 ≤ α ∧ ∃ ρ : Rule, ρ.α = ENNReal.ofReal α ∧
      D.real {y | α < y} ≤ 1 / b ∧ 1 / b ≤ D.real {y | α ≤ y} ∧
      (0 < D.real {α} → ρ.θ = (1 / b - D.real {y | α < y}) / D.real {α}) ∧
      acceptProb D ρ = 1 / b := by sorry

end EffHorizonProphet
