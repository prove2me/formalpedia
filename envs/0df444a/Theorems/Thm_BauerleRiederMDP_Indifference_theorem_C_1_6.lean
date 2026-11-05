-- Prove2me | Theorems.Thm_BauerleRiederMDP_Indifference_theorem_C_1_6
-- name    : BauerleRiederMDP.Indifference.theorem_C_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:30:09.791453+00:00
-- url     : https://prove2.me/theorems/d1a61d03-6d64-44ed-96ed-94894f85aac2
-- title:
--   Theorem C.1.6, first sentence — the price of an attainable claim is $\mathbb E_Q[H/S^0_N]$
-- statement:
--   Suppose there are no arbitrage opportunities and $Q$ is an equivalent martingale measure. Then the price of an attainable contingent claim $H$ can be computed by
--   $$
--   \pi(H)=\mathbb E_Q\Bigl[\frac{H}{S^0_N}\Bigr].
--   $$
--   Precisely: for every hedging strategy $\phi$ of $H$, the discounted payoff $H/S^0_N$ is $Q$-integrable and the initial value $X^\phi_0=\phi^0_0+\phi_0\cdot e$ equals this expectation.
--
--   This is the pricing rule with which Remark 4.9.3 compares the indifference price, so that the indifference pricing formula is consistent with the arbitrage free pricing formula.
--
--   **Formalization Note** The price is the initial value of a hedging strategy (Definition C.1.5), so the statement also says that it does not depend on the hedging strategy. Integrability is part of the conclusion, so the Bochner integral is the expectation.
--
--   Differences from the source:
--   - reading: the price of an attainable contingent claim H can be computed by π(H) = 𝔼_Q[H/S⁰_N] → Q-integrability of H/S⁰_N together with X^φ₀ = 𝔼_Q[H/S⁰_N] for every hedging strategy φ of H; reason: the expectation must exist for the formula to mean anything, and π(H) is defined through any hedging strategy
--   - reading: initial prices s^k₀ deterministic → s^k₀ > 0; reason: s^k₀ is the price of asset k, which the book keeps positive (p.61); at s^k₀ = 0 the martingale condition leaves R̃^k free and the formula fails
--   - encoding: an N-period market → 0 < N; reason: a strategy has an initial portfolio (φ⁰₀, φ₀) only when N ≥ 1, and π(H) is defined through it
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem C.1.6, p.366

import Mathlib
import Definitions.Def_BauerleRiederMDP_Indifference_FinancialMarket_NoArbitrage
import Definitions.Def_BauerleRiederMDP_Indifference_FinancialMarket_IsEMM
import Definitions.Def_BauerleRiederMDP_Indifference_FinancialMarket_IsHedging

open MeasureTheory

namespace BauerleRiederMDP.Indifference

/-- Theorem C.1.6, first sentence (Bäuerle & Rieder, Markov Decision Processes with Applications to
Finance (2011), Theorem C.1.6, p.366, PDF 371). Suppose there are no arbitrage opportunities and `Q`
is an equivalent martingale measure. Then the price of an attainable contingent claim `H` can be
computed by `π(H) = 𝔼_Q[H/S⁰_N]`.

**Formalization Note.** `φ` is any hedging strategy of `H`, and `π(H) = X^φ₀` (Definition C.1.5), so
the statement also says that the price does not depend on the hedging strategy. The integrability
of `H/S⁰_N` under `Q` is part of the conclusion, so that the Bochner integral is the expectation. -/
theorem theorem_C_1_6 {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ} (M : FinancialMarket Ω d N)
    (hNA : M.NoArbitrage) {Q : Measure Ω} (hQ : M.IsEMM Q) {H : Ω → ℝ}
    (hH : M.IsContingentClaim H) (φ : M.Strategy) (hφ : FinancialMarket.IsHedging φ H) :
    Integrable (fun ω => H ω / M.S0 N) Q ∧
      ∀ ω, FinancialMarket.X φ 0 ω = ∫ ω', H ω' / M.S0 N ∂Q := by sorry

end BauerleRiederMDP.Indifference
