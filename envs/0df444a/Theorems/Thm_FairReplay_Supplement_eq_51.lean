-- Prove2me | Theorems.Thm_FairReplay_Supplement_eq_51
-- name    : FairReplay.Supplement.eq_51
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:55:46.759092+00:00
-- url     : https://prove2.me/theorems/8e088acf-c001-4854-aa95-ec3c18e81094
-- title:
--   Theorem 10.5, eq. (51) — $Q_{\mathrm{thr}}=\Theta((\tau+d)\log(1/\delta)/d^2)$ when $r-d$ is bounded below
-- statement:
--   With $r=1-p-s-\tau$ and $X=\frac{\tau+d}{d^2}\log\frac1\delta$:
--
--   1. for every $\rho>0$ and $\delta\in(0,1/2)$ there are constants $c,C>0$ such that, for all P18 parameters ($p>0$, $s\ge0$, $\tau\ge0$, $d>0$, $p+s+\tau+d<1$) with $r-d\ge\rho$,
--   $$c\,X\ \le\ Q_{\mathrm{thr}}^{\mathrm{pair}}\ \le\ Q_{\mathrm{thr}}^{\mathrm{comp}}\ \le\ C\,X;$$
--   2. hence $\tau=O(d)$ retains $d^{-1}$ scaling: for fixed $p,s$ with $p+s<1$, $\delta$ and $\kappa\ge0$, both quantities are of order $\log(1/\delta)/d$ for all small $d$ and $0\le\tau\le\kappa d$;
--   3. and every fixed $\tau>0$ (with $p+s+\tau<1$) restores $d^{-2}$ scaling: both quantities are of order $\log(1/\delta)/d^2$ for all small $d$.
--
--   $Q_{\mathrm{thr}}^{\mathrm{pair}}$ is the optimal null expected number of four-way rounds for the boundary pair, $Q_{\mathrm{thr}}^{\mathrm{comp}}$ the same over testers correct for the whole composite problem (49).
--
--   Differences from the source:
--   - reading: Q_thr(τ, d, δ) (no definition given) → two quantities, QthrPair (boundary pair) and QthrComp (composite problem (49)), both bounded; reason: both natural readings are covered; the sandwich Q^pair ≤ Q^comp is stated
--   - reading: Θ(·) up to constants, if r − d is bounded below by a positive constant, as d → 0 → for every ρ > 0 constants c, C depending only on ρ and δ, uniformly over all P18 parameters with r − d ≥ ρ; reason: the uniform reading is the stronger one and implies the fixed-parameter asymptotics
--   - encoding: τ = O(d) retains d⁻¹ scaling; fixed τ > 0 restores d⁻² → items 2 and 3 with explicit constants c, C, d₀ chosen before d; reason: the Θ convention of the published Theorem 10.4
--   - encoding: Q (no displayed definition) → the infimum in [0, ∞] of the null expected stopping time over δ-correct testers; reason: the paper's own usage ("optimal expected null declared cost", p.20); the reading of the published Theorem 10.4
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.5, eq. (51), p.16 (PDF p.18)

import Mathlib
import Definitions.Def_FairReplay_Supplement_Qthr

namespace FairReplay.Supplement

/-- **Theorem 10.5, eq. (51), the thresholded phase transition** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0…), Theorem 10.5, eq. (51), p.16
(PDF p.18)): "If r − d is bounded below by a positive constant, then as d → 0 with δ fixed these bounds
give Qthr(τ, d, δ) = Θ((τ + d)/d² log 1/δ) (51) up to constants. Hence τ = 0 and, more generally,
τ = O(d) retain d−1 scaling, whereas every fixed τ > 0 restores d−2 scaling as d → 0."

With `r = 1 − p − s − τ` and `X = (τ + d) log(1/δ)/d²`:
1. for every `ρ > 0` and `δ ∈ (0, 1/2)` there are `c, C > 0` such that, for all P18 parameters
   (`p > 0`, `s ≥ 0`, `τ ≥ 0`, `d > 0`, `p + s + τ + d < 1`) with `r − d ≥ ρ`,
   `c X ≤ Q_thr^pair ≤ Q_thr^comp ≤ C X`;
2. (`τ = O(d)`) for fixed `p, s` with `p + s < 1`, `δ` and `κ ≥ 0`, there are `c, C, d₀ > 0` with
   `c log(1/δ)/d ≤ Q_thr^pair` and `Q_thr^comp ≤ C log(1/δ)/d` for all `d ∈ (0, d₀)` and `0 ≤ τ ≤ κ d`;
3. (fixed `τ > 0`) for fixed `p, s, τ` with `p + s + τ < 1` and `δ`, there are `c, C, d₀ > 0` with
   `c log(1/δ)/d² ≤ Q_thr^pair` and `Q_thr^comp ≤ C log(1/δ)/d²` for all `d ∈ (0, d₀)`.

**Formalization Note** The paper does not define `Q_thr`; both readings are bounded:
`Q_thr^pair` is the optimal null expected number of rounds for the boundary null against the
alternative, and `Q_thr^comp` the same over testers correct for the whole composite problem (49).
"Up to constants" is read uniformly: the constants depend only on `ρ` and `δ` (item 1). -/
theorem eq_51 :
    (∀ ρ δ : ℝ, 0 < ρ → 0 < δ → δ < 1 / 2 →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ p s τ d : ℝ, 0 < p → 0 ≤ s → 0 ≤ τ → 0 < d → p + s + τ + d < 1 →
          ρ ≤ (1 - p - s - τ) - d →
          ENNReal.ofReal (c * ((τ + d) * Real.log (1 / δ) / d ^ 2)) ≤ QthrPair p s τ d δ ∧
          QthrPair p s τ d δ ≤ QthrComp p s τ d δ ∧
          QthrComp p s τ d δ ≤ ENNReal.ofReal (C * ((τ + d) * Real.log (1 / δ) / d ^ 2))) ∧
    (∀ p s δ κ : ℝ, 0 < p → 0 ≤ s → p + s < 1 → 0 < δ → δ < 1 / 2 → 0 ≤ κ →
      ∃ c C d₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < d₀ ∧
        ∀ d τ : ℝ, 0 < d → d < d₀ → 0 ≤ τ → τ ≤ κ * d →
          ENNReal.ofReal (c * Real.log (1 / δ) / d) ≤ QthrPair p s τ d δ ∧
          QthrComp p s τ d δ ≤ ENNReal.ofReal (C * Real.log (1 / δ) / d)) ∧
    (∀ p s τ δ : ℝ, 0 < p → 0 ≤ s → 0 < τ → p + s + τ < 1 → 0 < δ → δ < 1 / 2 →
      ∃ c C d₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < d₀ ∧
        ∀ d : ℝ, 0 < d → d < d₀ →
          ENNReal.ofReal (c * Real.log (1 / δ) / d ^ 2) ≤ QthrPair p s τ d δ ∧
          QthrComp p s τ d δ ≤ ENNReal.ofReal (C * Real.log (1 / δ) / d ^ 2)) := by sorry

end FairReplay.Supplement
