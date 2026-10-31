-- Prove2me | Theorems.Thm_BlockchainMarketPower_util_b
-- name    : BlockchainMarketPower.util_b
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:27:04.081205+00:00
-- url     : https://prove2.me/theorems/d4bf0d11-60dc-458d-ab9c-21a72f35a0b4
-- title:
--   Utility with blockchain: $\mathcal M_{\mathcal B}=f(P,\Psi;\gamma/|\Xi|)$ or at most $0$
-- statement:
--   Consider any strategy in which suppliers play a symmetric effort after every history, and a valid order $(P,\Psi,\Xi)$, for either manufacturer type. If $\Xi\ne\emptyset$ and $0<\Psi<P\le 2(\alpha+\delta(1-\alpha))-1$, then
--
--   $$
--   \mathcal M_{\mathrm{B}}=\tfrac12(P-\Psi)\Psi-\tfrac{\gamma}{8|\Xi|}(P-\Psi)^2\Psi(1-\Psi)=f\bigl(P,\Psi;\tfrac{\gamma}{|\Xi|}\bigr).
--   $$
--
--   At every other valid order, $\mathcal M_{\mathrm{B}}\le 0$.
--
--   The dependence on $|\Xi|$ is the diversification effect of traceability: only the defective batch is recalled, so the profit variance falls with the number of suppliers.
--
--   Differences from the source:
--   - reading: §3.1: accept and effort are simultaneous and (2) depends on the accepting set Γ → symmetric fixed point with exponent |Ξ| - 1, assuming all of Ξ produce, then acceptance tested at that effort; reason: this is what the proof computes on pp.32, 36; the paper names no other solution of the supplier stage
--   - encoding: (1) with the factor Q → profit per unit, for every Ξ ≠ ∅; reason: the proof drops Q on p.32; nothing changes when Q > 0, and (1) is identically 0 when Q = 0
--   - reading: the law of the batches is not specified → independent batches, on the sample space Fin N → Bool with success probability 1 - ρ(e) = √e; reason: (2) multiplies the survival probabilities and the factor 1/|Ξ| on p.38 requires independence
--   - encoding: (8) integrates I(C_k ≥ v₀) over consumers k ∈ [0, 1] → the purchase probability of a generic consumer, given the manufacturer type q; reason: independent signals on a continuum make the integral not literally definable; this is the value the paper assigns to it
--   - reading: (7) conditions on (q̃_k, P) → the expectation conditions on the consumer type and the signal (t, q̃); reason: without t_k the expectation would be v₀ - P for every consumer; the proof on p.31 conditions on (t_k, q̃_k)
--   - encoding: N ∈ ℕ; α ∈ [α̲, ᾱ] with 1/2 < α̲ < ᾱ < 1; suppliers {1, ..., N} → 0 < N; 1/2 < α < 1; suppliers Fin N; reason: the same instances
-- source:
--   Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, proof of Proposition 3.1, p.38

import Mathlib
import Definitions.Def_BlockchainMarketPower_Model

namespace BlockchainMarketPower

/-- Utility with blockchain, Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, proof of Proposition 3.1, p.38:
after any symmetric supplier response, `𝓜_B = f(P, Ψ; γ/|Ξ|)` at a valid order with `Ξ ≠ ∅` and
`0 < Ψ < P ≤ 2(α + δ(1 - α)) - 1`, and `𝓜_B ≤ 0` at every other valid order. The factor `1/|Ξ|` is the
variance of the average of `|Ξ|` independent indicators. -/
theorem util_b {N : ℕ} (p : Params N) (σ : Strategy N) (hσ : σ.SuppliersRespond) (q : Bool)
    (x : Order N) (hx : x.Valid) :
    (x.Ξ.Nonempty ∧ 0 < x.Ψ ∧ x.Ψ < x.P ∧ x.P ≤ 2 * (p.α + p.δ * (1 - p.α)) - 1 →
        p.util σ .B q x = f x.P x.Ψ (p.γ / (x.Ξ.card : ℝ))) ∧
      (¬ (x.Ξ.Nonempty ∧ 0 < x.Ψ ∧ x.Ψ < x.P ∧ x.P ≤ 2 * (p.α + p.δ * (1 - p.α)) - 1) →
        p.util σ .B q x ≤ 0) := by sorry

end BlockchainMarketPower
