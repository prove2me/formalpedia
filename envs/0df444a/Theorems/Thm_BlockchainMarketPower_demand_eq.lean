-- Prove2me | Theorems.Thm_BlockchainMarketPower_demand_eq
-- name    : BlockchainMarketPower.demand_eq
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:26:46.349228+00:00
-- url     : https://prove2.me/theorems/2bfafdea-60d1-4c50-8f88-0c1a1994b2ad
-- title:
--   Proposition 3.1 part 1: equilibrium consumer demand
-- statement:
--   Let $P\ge 0$. For either manufacturer type, consumer demand in the two regimes is
--
--   $$
--   s^\star_{\mathrm{NB}}=\tfrac12\,I\bigl(P\le 2\alpha-1\bigr),\qquad s^\star_{\mathrm{B}}=\tfrac12\,I\bigl(P\le 2(\alpha+\delta(1-\alpha))-1\bigr).
--   $$
--
--   Demand here is the Bayes-rational purchase probability of the model, so this statement reduces the consumer layer to a threshold in the price.
--
--   Differences from the source:
--   - encoding: (8) integrates I(C_k ≥ v₀) over consumers k ∈ [0, 1] → the purchase probability of a generic consumer, given the manufacturer type q; reason: independent signals on a continuum make the integral not literally definable; this is the value the paper assigns to it
--   - reading: (7) conditions on (q̃_k, P) → the expectation conditions on the consumer type and the signal (t, q̃); reason: without t_k the expectation would be v₀ - P for every consumer; the proof on p.31 conditions on (t_k, q̃_k)
--   - encoding: N ∈ ℕ; α ∈ [α̲, ᾱ] with 1/2 < α̲ < ᾱ < 1; suppliers {1, ..., N} → 0 < N; 1/2 < α < 1; suppliers Fin N; reason: the same instances
-- source:
--   Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, Proposition 3.1 part 1, p.17

import Mathlib
import Definitions.Def_BlockchainMarketPower_Model

namespace BlockchainMarketPower

/-- Proposition 3.1 part 1, Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, p.17 (proof pp.31, 36):
for `P ≥ 0`, equilibrium consumer demand is `s_NB = (1/2) I(P ≤ 2α - 1)` and
`s_B = (1/2) I(P ≤ 2(α + δ(1 - α)) - 1)`, for either manufacturer type.

**Formalization Note.** Demand is the Bayes quotient `demandAt`, not this closed form. -/
theorem demand_eq {N : ℕ} (p : Params N) (q : Bool) (P : ℝ) (hP : 0 ≤ P) :
    p.demand .NB q P = 1 / 2 * (if P ≤ 2 * p.α - 1 then 1 else 0) ∧
      p.demand .B q P =
        1 / 2 * (if P ≤ 2 * (p.α + p.δ * (1 - p.α)) - 1 then 1 else 0) := by sorry

end BlockchainMarketPower
