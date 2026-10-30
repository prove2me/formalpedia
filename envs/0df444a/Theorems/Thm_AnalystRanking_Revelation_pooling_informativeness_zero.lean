-- Prove2me | Theorems.Thm_AnalystRanking_Revelation_pooling_informativeness_zero
-- name    : AnalystRanking.Revelation.pooling_informativeness_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:53:03.418774+00:00
-- url     : https://prove2.me/theorems/c0a3ccb2-3a62-4982-ad60-e293c9f28574
-- title:
--   Pooling strategies have zero forecast informativeness
-- statement:
--   Standing assumptions (§2): $\gamma\in(\tfrac12,1)$, $\rho\in[0,1]$, $q\in(0,1)$. For every strategy $\sigma\in[0,1]^2$ that is pooling, $\sigma^h+\sigma^l=1$,
--   $$\Pi(\sigma)=0 .$$
--
--   A pooling forecast does not depend on the signal, so the forecasts reveal nothing the market did not know.
--
--   Differences from the source:
--   - generalization: for a pooling equilibrium → for every pooling strategy σ ∈ [0,1]² (σh + σl = 1); reason: the argument uses only that the forecast law does not depend on the signal; it specializes to pooling equilibria
--   - reading: display before (1), p. 7: Pr(si, sj | ω) = 2(1 − ρ)γ(1 − γ) if si ≠ sj → (1 − ρ)γ(1 − γ) for each ordered discordant pair, per (1)–(2); reason: the printed value is the probability of the event si ≠ sj; per ordered pair only (1)–(2) sum to 1
--   - encoding: Π of (6) with H = 1, L = 0 → informativeness, with x/0 = 0 for a forecast pair of probability 0; reason: such a pair contributes 0 to the expected posterior variance, its true contribution
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), §5, p. 24, unnumbered

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_informativeness

namespace AnalystRanking.Revelation

/-- **Pooling equilibria have zero forecast informativeness.**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), §5, p. 24, unnumbered: "For a pooling equilibrium, forecast informativeness is zero because
no additional information is revealed by the analysts that the market did not know." A strategy
is pooling if `σʰ = 1 − σˡ` (p. 9).

**Formalization Note.** Stated for every pooling strategy `σ ∈ [0, 1]²` with `σʰ + σˡ = 1`
(equilibrium or not), with `Π` of Definition 3 (`H = 1`, `L = 0`). -/
theorem pooling_informativeness_zero (γ ρ q : ℝ) (σ : ℝ × ℝ) (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hσ1 : 0 ≤ σ.1) (hσ1' : σ.1 ≤ 1) (hσ2 : 0 ≤ σ.2) (hσ2' : σ.2 ≤ 1) (hpool : σ.1 + σ.2 = 1) :
    informativeness q γ ρ σ = 0 := by sorry

end AnalystRanking.Revelation
