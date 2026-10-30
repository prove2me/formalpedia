-- Prove2me | Theorems.Thm_AnalystRanking_Revelation_claim_7_informativeness_monotone
-- name    : AnalystRanking.Revelation.claim_7_informativeness_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:54:06.13999+00:00
-- url     : https://prove2.me/theorems/57b19b6e-7d34-42ad-b23d-f00f3838eaf3
-- title:
--   Claim 7: forecast informativeness increases in $\sigma^h$ and $\sigma^l$ (corrected: corner $\rho=1$, $\sigma=(1,1)$ excluded from the derivative clauses)
-- statement:
--   Standing assumptions (§2): $\gamma\in(\tfrac12,1)$, $\rho\in[0,1]$, $q\in(0,1)$. On the informative region $\sigma\in[0,1]^2$, $\sigma^h>1-\sigma^l$:
--
--   1. except at the single point $\rho=1$, $\sigma=(1,1)$, the derivatives (within $[0,1]$, one-sided at an endpoint) satisfy
--   $$\frac{\partial\Pi(\sigma^h,\sigma^l)}{\partial\sigma^h}>0,\qquad\frac{\partial\Pi(\sigma^h,\sigma^l)}{\partial\sigma^l}>0;$$
--   2. $\Pi$ is strictly increasing: if $\sigma\le\sigma'$ coordinatewise, $\sigma\neq\sigma'$, both in $[0,1]^2$ and $\sigma^h+\sigma^l>1$, then $\Pi(\sigma)<\Pi(\sigma')$.
--
--   This converts the coordinatewise comparisons of equilibria in Proposition 3 into comparisons of informativeness, which is how Proposition 5 is proved.
--
--   Differences from the source:
--   - correction: for any σh > 1 − σl, ∂Π/∂σh > 0 and ∂Π/∂σl > 0 → the derivative clauses exclude ρ = 1 ∧ σ = (1,1); reason: there H1 = H2 = 0 in (B.60)–(B.61) and both one-sided derivatives are 0 (e.g. γ = 0.7, q = 0.6, ρ = 1)
--   - reading: 'forecast informativeness is monotone increasing in equilibrium informativeness' → strict increase of Π along the coordinatewise order on the informative region; reason: the claim's first sentence; it holds on the whole region including the excluded corner
--   - reading: display before (1), p. 7: Pr(si, sj | ω) = 2(1 − ρ)γ(1 − γ) if si ≠ sj → (1 − ρ)γ(1 − γ) for each ordered discordant pair, per (1)–(2); reason: the printed value is the probability of the event si ≠ sj; per ordered pair only (1)–(2) sum to 1
--   - encoding: ∂Π/∂σh, ∂Π/∂σl on σ ∈ [0,1]² → HasDerivWithinAt … (Set.Icc 0 1); reason: derivatives at σh = 1 or σl = 1 are one-sided, as on the boundary of the strategy square
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 7, p. 55; proof pp. 55–59, (B.60)–(B.61), p. 59

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_informativeness

namespace AnalystRanking.Revelation

/-- **Claim 7: forecast informativeness increases with equilibrium informativeness (corner corrected).**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 7, p. 55: "For any informative equilibrium, forecast informativeness is monotone
increasing in equilibrium informativeness. That is, for any `σʰ > 1 − σˡ`,
i) `∂Π(σʰ, σˡ)/∂σʰ > 0`, ii) `∂Π(σʰ, σˡ)/∂σˡ > 0`."

**Formalization Note.** Correction: at the single point `ρ = 1`, `σ = (1, 1)` both one-sided
derivatives are `0` (`H₁ = H₂ = 0` in (B.60)–(B.61), and the discordant forecast pair has
probability `0`), so the derivative clauses exclude it. Derivatives are taken within `[0, 1]`
(one-sided at an endpoint). The monotonicity clause holds on the whole informative region,
including that corner. -/
theorem claim_7_informativeness_monotone (γ ρ q : ℝ) (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    (∀ σ : ℝ × ℝ, 0 ≤ σ.1 → σ.1 ≤ 1 → 0 ≤ σ.2 → σ.2 ≤ 1 → 1 < σ.1 + σ.2 →
      ¬ (ρ = 1 ∧ σ = (1, 1)) →
      (∃ d : ℝ, 0 < d ∧
        HasDerivWithinAt (fun x => informativeness q γ ρ (x, σ.2)) d (Set.Icc 0 1) σ.1) ∧
      (∃ d : ℝ, 0 < d ∧
        HasDerivWithinAt (fun x => informativeness q γ ρ (σ.1, x)) d (Set.Icc 0 1) σ.2)) ∧
    (∀ σ σ' : ℝ × ℝ, 0 ≤ σ.1 → σ'.1 ≤ 1 → 0 ≤ σ.2 → σ'.2 ≤ 1 → 1 < σ.1 + σ.2 →
      σ.1 ≤ σ'.1 → σ.2 ≤ σ'.2 → σ ≠ σ' →
      informativeness q γ ρ σ < informativeness q γ ρ σ') := by sorry

end AnalystRanking.Revelation
