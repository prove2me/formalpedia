-- Prove2me | Theorems.Thm_FairReplay_Supplement_eq_25
-- name    : FairReplay.Supplement.eq_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:53:43.164325+00:00
-- url     : https://prove2.me/theorems/a64d9325-2dbb-4974-a5a7-a15635ab9876
-- title:
--   Theorem 10.3, eq. (25) — $Q_{\mathrm{pair}}=\Theta(\log(1/\delta)/d)$ and $Q_{\mathrm{ind}}=\Theta(\log(1/\delta)/d^2)$
-- statement:
--   For every fixed $p\in(0,1)$ and $\delta\in(0,1/2)$, as $d\to0$,
--   $$Q_{\mathrm{pair}}(d,\delta)=\Theta\Big(\frac{\log(1/\delta)}{d}\Big),\qquad Q_{\mathrm{ind}}(d,\delta)=\Theta\Big(\frac{\log(1/\delta)}{d^2}\Big),$$
--   with constants depending on $p$ and $\delta$. Here $Q_{\mathrm{pair}}$ and $Q_{\mathrm{ind}}$ are the optimal null expected numbers of rounds of $\delta$-correct testers under raw-pair replay and under independent single-execution observation of the one-edge family.
--
--   Replay thus changes the small-patch exponent from $d^{-2}$ to $d^{-1}$ even without a common shift.
--
--   Differences from the source:
--   - encoding: Q (no displayed definition) → the infimum in [0, ∞] of the null expected stopping time over δ-correct testers; reason: the paper's own usage ("optimal expected null declared cost", p.20); the reading of the published Theorem 10.4
--   - encoding: Θ(·) as d → 0 with the other parameters fixed → ∃ c, C, d₀ > 0 chosen before d (depending only on the fixed parameters) with c·X ≤ Q ≤ C·X for d ∈ (0, d₀); d₀ inside the theorem's domain; reason: the reading of the published Theorem 10.4, eq. (37)
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.3, eq. (25), p.13 (PDF p.15)

import Mathlib
import Definitions.Def_FairReplay_Supplement_indepModel

namespace FairReplay.Supplement

/-- **Theorem 10.3, eq. (25), the Θ rates of paired versus independent observation** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0…), Theorem
10.3, eq. (25), p.13 (PDF p.15)): "Consequently, for every fixed interior p, Qpair(d, δ) =
Θ(log(1/δ)/d), Qind(d, δ) = Θ(log(1/δ)/d²) (25) as d → 0 with p and δ fixed, up to constants
depending on them."

For every fixed `p ∈ (0, 1)` and `δ ∈ (0, 1/2)` there are `c, C, d₀ > 0` (depending on `p, δ`, chosen
before `d`) such that for every `d ∈ (0, d₀)`:
`c log(1/δ)/d ≤ Q_pair(d, δ) ≤ C log(1/δ)/d` and `c log(1/δ)/d² ≤ Q_ind(d, δ) ≤ C log(1/δ)/d²`.

**Formalization Note** `Q_pair` and `Q_ind` are the infima, in `[0, ∞]`, of the null expected number of
rounds over δ-correct testers of the raw-pair model (`vertexModel p 0 d`) and of the independent
single-execution model (`indepModel p d`). `Θ` is read as in the published Theorem 10.4, eq. (37):
constants chosen before `d`. `d₀ ≤ 1 − p` keeps every `d` inside the theorem's domain. -/
theorem eq_25 :
    ∀ p δ : ℝ, 0 < p → p < 1 → 0 < δ → δ < 1 / 2 →
      ∃ c C d₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < d₀ ∧ d₀ ≤ 1 - p ∧
        ∀ d : ℝ, 0 < d → d < d₀ →
          ENNReal.ofReal (c * Real.log (1 / δ) / d) ≤ Qpair p d δ ∧
          Qpair p d δ ≤ ENNReal.ofReal (C * Real.log (1 / δ) / d) ∧
          ENNReal.ofReal (c * Real.log (1 / δ) / d ^ 2) ≤ Qind p d δ ∧
          Qind p d δ ≤ ENNReal.ofReal (C * Real.log (1 / δ) / d ^ 2) := by sorry

end FairReplay.Supplement
