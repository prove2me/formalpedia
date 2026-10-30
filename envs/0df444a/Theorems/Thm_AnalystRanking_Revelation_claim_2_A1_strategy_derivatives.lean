-- Prove2me | Theorems.Thm_AnalystRanking_Revelation_claim_2_A1_strategy_derivatives
-- name    : AnalystRanking.Revelation.claim_2_A1_strategy_derivatives
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:47:30.052785+00:00
-- url     : https://prove2.me/theorems/8bc705da-daac-4b5b-a4ba-d1ba045de4e7
-- title:
--   Claim 2 (A.1): strategy derivatives of $\Psi$ and $\Delta U$ under convex payoffs (corrected: cross derivatives need $\rho<1$)
-- statement:
--   Standing assumptions (§2): $\gamma\in(\tfrac12,1)$, $\rho\in[0,1]$, $q\in(0,1)$, and rank payoffs $w_1>w_0>w_2$ with convexity $\varphi=(w_1-w_0)/(w_0-w_2)$. Suppose $\varphi>1$ and let the other analyst play $\sigma\in[0,1]^2$. Then
--   $$\frac{\partial\Psi^h_i}{\partial\sigma^h}>0,\quad \frac{\partial\Psi^l_i}{\partial\sigma^l}<0,\quad \frac{\partial\Delta U^h_i}{\partial\sigma^h}<0,\quad \frac{\partial\Delta U^l_i}{\partial\sigma^l}<0,$$
--   and, if $\rho<1$, also
--   $$\frac{\partial\Psi^l_i}{\partial\sigma^h}>0,\quad \frac{\partial\Psi^h_i}{\partial\sigma^l}<0,\quad \frac{\partial\Delta U^l_i}{\partial\sigma^h}>0,\quad \frac{\partial\Delta U^h_i}{\partial\sigma^l}>0 .$$
--
--   Under convex payoffs, the more truthful the other analyst, the stronger the incentive to differentiate from him.
--
--   Differences from the source:
--   - correction: for any k ∈ {h,l}, ∂Ψk/∂σh > 0 > ∂Ψk/∂σl, and ∂ΔUl/∂σh > 0, ∂ΔUh/∂σl > 0, for every ρ → the four cross derivatives (∂Ψl/∂σh, ∂Ψh/∂σl, ∂ΔUl/∂σh, ∂ΔUh/∂σl) only for ρ < 1; reason: at ρ = 1, γ − χ/(1−γ) = 1 − γ − χ/γ = 0, so Ψh does not depend on σl nor Ψl on σh and the cross derivatives are 0; e.g. γ = 0.7, φ = 2, ρ = 1, σ = (0.6, 0.7): ∂Ψh/∂σl = 0
--   - encoding: signals {h,l}, forecasts {ĥ,l̂}, states {H,L}; strategy (σh, σl); payoffs w1 > w0 > w2 of (3) → Bool with true the high value; σ : ℝ × ℝ; the payoff triple (w1, w0, w2) with φ = phiConvexity w1 w0 w2; reason: Lean convention; same instances
--   - reading: display before (1), p. 7: Pr(si, sj | ω) = 2(1 − ρ)γ(1 − γ) if si ≠ sj → (1 − ρ)γ(1 − γ) for each ordered discordant pair, per (1)–(2); reason: the printed value is the probability of the event si ≠ sj; per ordered pair only (1)–(2) sum to 1
--   - encoding: partial derivatives ∂/∂σh, ∂/∂σl → Mathlib deriv of the one-variable section; reason: deriv is 0 where the function is not differentiable, so a strict sign also asserts differentiability, as the paper's derivative presupposes
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 2 (A.1), p. 34

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_psiH
import Definitions.Def_AnalystRanking_Revelation_psiL
import Definitions.Def_AnalystRanking_Revelation_dUh
import Definitions.Def_AnalystRanking_Revelation_dUl
import Definitions.Def_AnalystRanking_Revelation_phiConvexity

namespace AnalystRanking.Revelation

/-- **Claim 2 (A.1): signs of the strategy derivatives under convex payoffs (corrected at `ρ = 1`).**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 2 (A.1), p. 34: "Suppose `φ > 1`. For any `k ∈ {h, l}`,
`∂Ψᵏ_i/∂σʰ > 0 > ∂Ψᵏ_i/∂σˡ`, and thus, `∂ΔUʰ_i/∂σʰ < 0 < ∂ΔUˡ_i/∂σʰ` and
`∂ΔUˡ_i/∂σˡ < 0 < ∂ΔUʰ_i/∂σˡ`."

**Formalization Note.** Correction: the four cross derivatives `∂Ψʰ/∂σˡ`, `∂Ψˡ/∂σʰ`, `∂ΔUˡ/∂σʰ`,
`∂ΔUʰ/∂σˡ` vanish at `ρ = 1` (then `γ − χ/(1−γ) = 1 − γ − χ/γ = 0` in (A.11)–(A.12): `Ψʰ` does
not depend on `σˡ` nor `Ψˡ` on `σʰ`), so their strict signs are stated for `ρ < 1`; the four own
derivatives hold for every `ρ ∈ [0, 1]`. `σ ∈ [0, 1]²` is the other analyst's strategy; `deriv`
is Mathlib's derivative (it is `0` where the function is not differentiable, so a strict sign
also asserts differentiability). -/
theorem claim_2_A1_strategy_derivatives (γ ρ q w1 w0 w2 : ℝ) (σ : ℝ × ℝ) (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hw20 : w2 < w0) (hw01 : w0 < w1) (hσ1 : 0 ≤ σ.1) (hσ1' : σ.1 ≤ 1) (hσ2 : 0 ≤ σ.2) (hσ2' : σ.2 ≤ 1)
    (hφ : 1 < phiConvexity w1 w0 w2) :
    0 < deriv (fun x => psiH γ ρ (phiConvexity w1 w0 w2) (x, σ.2)) σ.1 ∧
      deriv (fun x => psiL γ ρ (phiConvexity w1 w0 w2) (σ.1, x)) σ.2 < 0 ∧
      deriv (fun x => dUh w1 w0 w2 q γ ρ (x, σ.2)) σ.1 < 0 ∧
      deriv (fun x => dUl w1 w0 w2 q γ ρ (σ.1, x)) σ.2 < 0 ∧
      (ρ < 1 →
        0 < deriv (fun x => psiL γ ρ (phiConvexity w1 w0 w2) (x, σ.2)) σ.1 ∧
          deriv (fun x => psiH γ ρ (phiConvexity w1 w0 w2) (σ.1, x)) σ.2 < 0 ∧
          0 < deriv (fun x => dUl w1 w0 w2 q γ ρ (x, σ.2)) σ.1 ∧
          0 < deriv (fun x => dUh w1 w0 w2 q γ ρ (σ.1, x)) σ.2) := by sorry

end AnalystRanking.Revelation
