-- Prove2me | Theorems.Thm_EffHorizonProphet_Supplement_theorem_10
-- name    : EffHorizonProphet.Supplement.theorem_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:06:35.830932+00:00
-- url     : https://prove2.me/theorems/ec0f02d0-b619-46a5-bef4-23e64328127d
-- title:
--   Theorem 10 — the infinite-horizon rule with acceptance probability $1-\tilde\gamma$ has $\mathrm{CR}_\infty\ge1/(1+\tilde\gamma)$
-- statement:
--   Fix $0<\tilde\gamma<1$ and an admissible base law $D$, with $Y_1,Y_2,\dots$ i.i.d. from $D$ and $X_i=\tilde\gamma^{i-1}Y_i$. Choose a base threshold $\alpha$ with
--   $$P(Y>\alpha)\le1-\tilde\gamma\le P(Y\ge\alpha),$$
--   and a tie-breaking probability $\theta$ so that the per-stage acceptance probability $P(Y>\alpha)+\theta\,P(Y=\alpha)$ is exactly $1-\tilde\gamma=1/B_\infty$, where $B_\infty=\sum_{i\ge1}\tilde\gamma^{i-1}$. At stage $i$ the rule accepts if $X_i>\tilde\gamma^{i-1}\alpha$, or if $X_i=\tilde\gamma^{i-1}\alpha$ and an independent uniform coin $U_i\le\theta$, and it stops at the first acceptance. Then
--   $$\mathbb E_D[X_\tau]\ \ge\ \frac1{1+\tilde\gamma}\,\mathbb E_D\Big[\sup_{i\ge1}X_i\Big],$$
--   so $\mathrm{CR}_\infty(\tau)\ge1/(1+\tilde\gamma)$. Together with Theorem 9 this shows that the calibration $1/B_\infty$ is minimax optimal.
--
--   Differences from the source:
--   - encoding: a threshold $\alpha$ with $P(Y>\alpha)\le1-\tilde\gamma\le P(Y\ge\alpha)$ and randomization at ties so that the acceptance probability is exactly $1-\tilde\gamma$ → any `Rule` (threshold $\alpha\in[0,\infty]$, tie-break $\theta\in[0,1]$) with acceptance probability $1-\tilde\gamma$ under $D$; reason: the two classes coincide: such a rule satisfies the two inequalities, and $\alpha=\top$ is excluded because its acceptance probability is $0$
--   - encoding: acceptance $X_i>\tilde\gamma^{i-1}\alpha$ → acceptance $Y_i>\alpha$ (or a tie with $U_i\le\theta$), in the base scale; reason: the events coincide since $\tilde\gamma>0$
--   - encoding: $\mathrm{CR}_\infty(\tau)\ge\frac1{1+\tilde\gamma}$ → $\frac1{1+\tilde\gamma}\,\mathbb E_D[\sup_iX_i]\le\mathbb E_D[X_\tau]$ for every admissible $D$ and every such rule; reason: the infimum over $D$ of the ratio is at least $c$ exactly when each ratio is; the prophet value is finite and positive
--   - encoding: real-valued expectations → lower Lebesgue integrals in $[0,\infty]$; reason: for an admissible law both values are finite, so nothing changes; it avoids junk values
--   - encoding: stages $i=1,2,\dots$ → stages $0,1,\dots$; reason: a relabelling
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Theorem 10, p.12; proof in A.11, pp.52–53

import Mathlib
import Definitions.Def_EffHorizonProphet_IsAdmissible
import Definitions.Def_EffHorizonProphet_acceptProb
import Definitions.Def_EffHorizonProphet_Supplement_infGambler
import Definitions.Def_EffHorizonProphet_Supplement_infProphet

open MeasureTheory
open scoped ENNReal

namespace EffHorizonProphet.Supplement

/-- **Theorem 10** (guarantee of the calibrated quantile rule; Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), p.12; proof in A.11,
pp.52–53): fix `0 < γ̃ < 1`; choose a base threshold `α` with `P(Y > α) ≤ 1 − γ̃ ≤ P(Y ≥ α)` and
randomize at ties so that the acceptance probability is exactly `1 − γ̃`; at stage `i` use the value
threshold `γ̃^{i−1} α` and stop at the first acceptance. Then `CR_∞(τ) ≥ 1/(1 + γ̃)`.

**Formalization Note** The rule is any `Rule` (base threshold `α ∈ [0, ∞]` and tie-breaking
probability `θ`) whose per-stage acceptance probability under `D` is `1 − γ̃`; such rules are exactly
the page's thresholds with randomized ties. The bound holds for every admissible `D`, atoms
included, which is `CR_∞(τ) ≥ 1/(1 + γ̃)`. Values are in `ℝ≥0∞`. -/
theorem theorem_10 {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) {D : Measure ℝ}
    (hD : IsAdmissible D) (ρ : Rule) (hρ : acceptProb D ρ = 1 - γ) :
    ENNReal.ofReal (1 / (1 + γ)) * infProphet γ D ≤ infGambler γ D ρ := by sorry

end EffHorizonProphet.Supplement
