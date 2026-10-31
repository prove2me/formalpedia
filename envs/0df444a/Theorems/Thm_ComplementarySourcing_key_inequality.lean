-- Prove2me | Theorems.Thm_ComplementarySourcing_key_inequality
-- name    : ComplementarySourcing.key_inequality
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:07:48.477+00:00
-- url     : https://prove2.me/theorems/61e9f1a8-763b-4421-bedc-2e10f9b9de5c
-- title:
--   Proof of Theorem A1, p.A6, at $n=2$ — the key inequality, strict
-- statement:
--   Let $\mu>0$, $\alpha\ge0$ and $0\le\sigma<\epsilon_0$, put $\epsilon_1=\epsilon_0+\sigma$, $\epsilon_2=\epsilon_0-\sigma$, and suppose the sufficient condition of the proof of Theorem A1 at $n=2$,
--
--   $$r\mu\ge2\epsilon_1+\frac{\epsilon_1^2}{2\epsilon_2}.$$
--
--   With $k$, $x_k$ as in Proposition 2, $w^M=(\epsilon_k-x_k)/(\mu(1+\alpha x_k)^2)$ and $A_k$ as in (A4)–(A5),
--
--   $$w^M\mu A_k<(r-w^M)\mu A_k-\tfrac12x_k^2.$$
--
--   Combined with the closed forms (A4)–(A5), this says that the first mover earns strictly more than the price revenue of the second mover, which is what Theorem 2 needs. The hypotheses of Theorem 2 imply the condition above (item hypothesis_at_n_two).
--
--   Differences from the source:
--   - generalization: (r − w^M)µA_k − ½x_k² ≥ w^MµA_k → strict inequality; reason: stronger than the printed step, which it implies; Theorem 2 is strict, and at σ = 0, α = 0 the subtracted sums of (A5) vanish, so the strictness must come from here
--   - generalization: Theorem A1's hypothesis rµ ≥ 2ϵ_1 + max{(ϵ_0 − p_1ϵ_1)/p_1, ϵ_1²/(2ϵ_n)} → only rµ ≥ 2ϵ_1 + ϵ_1²/(2ϵ_n), the condition the step itself uses; reason: the step's algebra uses only this part, and k, x_k are defined by formulas that need nothing else, so the printed case is a specialization
--   - encoding: general n, p_i → n = 2, p_1 = p_2 = ½, ϵ_1 = ϵ0 + σ, ϵ_2 = ϵ0 − σ; reason: the substitution the page prescribes on p.A11 for the proof of Theorem 2; general n is not an item of this mission
--   - reading: µ is "a scaling parameter for market size" (p.7), and the page divides by µ (p.13) → 0 < μ; reason: a market-size scale is positive; the page's formulas are undefined at µ = 0
--   - reading: the condition divides by ϵ_n = ϵ_2 = ϵ0 − σ → σ < ε₀ (with 0 ≤ σ, so 0 < ε₂ ≤ ε₀); reason: the printed condition presupposes ϵ_n > 0
--   - encoding: x_1, x_2 as "the unique value" of Lemma 3 → reals x₁, x₂ with the predicates IsEffortCandidate1/2 as hypotheses; reason: Lemma 3 proves each predicate has exactly one solution, so the same numbers are meant
--   - encoding: index k ∈ {1, 2} → k : Fin 2 given by smallestMaxIndex, with x_k = ![x₁, x₂] k; reason: the paper's indices 1, 2 are 0, 1; same value of k
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), proof of Theorem A1, p.A6; n = 2 by the proof of Theorem 2, p.A11

import Mathlib
import Definitions.Def_ComplementarySourcing_IsEffortCandidate1
import Definitions.Def_ComplementarySourcing_IsEffortCandidate2
import Definitions.Def_ComplementarySourcing_candidateProfit1
import Definitions.Def_ComplementarySourcing_candidateProfit2
import Definitions.Def_ComplementarySourcing_smallestMaxIndex
import Definitions.Def_ComplementarySourcing_riskLevel
import Definitions.Def_ComplementarySourcing_weightedRisk

namespace ComplementarySourcing

/-- **The key inequality of the proof of Theorem A1**, `n = 2`: if `rµ ≥ 2ϵ₁ + ϵ₁²/(2ϵ_n)`, then
`(r − w^M) µ A_k − ½ x_k² > w^M µ A_k`, where `w^M = (ϵ_k − x_k)/(µ(1 + αx_k)²)`.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), proof of Theorem A1, p.A6 (PDF 34), and proof of Theorem 2, p.A11 (PDF 39).

**Formalization Note.** The page proves `≥` as its sufficient step. The strict form is needed:
at `σ = 0`, `α = 0` the second mover's effort is `0` at equilibrium, so the subtracted sums of (A5)
vanish and cannot supply the strictness of Theorem 2. It holds because `x_k > 0`. The hypothesis is
the page's own sufficient condition at `n = 2` (`ϵ_n = ϵ₂ = ϵ₀ − σ`, so `σ < ϵ₀`: the page divides
by `ϵ_n`); the hypotheses of Theorem 2 imply it (`hypothesis_at_n_two`). -/
theorem key_inequality {μ α r ε₀ σ x₁ x₂ π₁ π₂ xk wk : ℝ} {k : Fin 2}
    (hμ : 0 < μ) (hα : 0 ≤ α) (hσ₀ : 0 ≤ σ)
    (hx₁ : IsEffortCandidate1 α ε₀ σ x₁) (hx₂ : IsEffortCandidate2 α ε₀ σ x₂)
    (hπ₁ : π₁ = candidateProfit1 μ α r ε₀ σ x₁) (hπ₂ : π₂ = candidateProfit2 μ α r ε₀ σ x₂)
    (hk : k = smallestMaxIndex π₁ π₂) (hxk : xk = ![x₁, x₂] k)
    (hwk : wk = wholesaleCandidate μ α (riskLevel ε₀ σ k) xk)
    (hσ : σ < ε₀) (hr : r * μ ≥ 2 * (ε₀ + σ) + (ε₀ + σ) ^ 2 / (2 * (ε₀ - σ))) :
    wk * μ * weightedRisk ε₀ σ k < (r - wk) * μ * weightedRisk ε₀ σ k - 1 / 2 * xk ^ 2 := by sorry

end ComplementarySourcing
