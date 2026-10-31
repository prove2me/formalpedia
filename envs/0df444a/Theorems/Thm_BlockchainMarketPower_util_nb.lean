-- Prove2me | Theorems.Thm_BlockchainMarketPower_util_nb
-- name    : BlockchainMarketPower.util_nb
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:27:12.889993+00:00
-- url     : https://prove2.me/theorems/8e91ef5c-ff5d-4790-ac52-dafc7700a4cd
-- title:
--   Utility without blockchain: $\mathcal M_{\mathcal{NB}}=f(P,\Psi;\gamma)$ or at most $0$
-- statement:
--   Consider any strategy in which suppliers play a symmetric effort after every history, and a valid order $(P,\Psi,\Xi)$, for either manufacturer type. If $|\Xi|=1$ and $0<\Psi<P\le 2\alpha-1$, then
--
--   $$
--   \mathcal M_{\mathrm{NB}}=\tfrac12(P-\Psi)\Psi-\tfrac{\gamma}{8}(P-\Psi)^2\Psi(1-\Psi)=f(P,\Psi;\gamma).
--   $$
--
--   At every other valid order, $\mathcal M_{\mathrm{NB}}\le 0$.
--
--   This reduces the manufacturer's problem without blockchain to the maximization of an explicit function of $(P,\Psi)$. The order covered by the second clause includes $\Psi\ge1$ with $|\Xi|\ge2$, under any symmetric effort.
--
--   Differences from the source:
--   - generalization: the printed selection (e⋆_NB = 0 for |Ξ| > 1) → every symmetric supplier response after every history; reason: the printed selection is such a response (accepts_nb, effort_b), so the printed claim is a special case
--   - reading: §3.1: accept and effort are simultaneous and (2) depends on the accepting set Γ → symmetric fixed point with exponent |Ξ| - 1, assuming all of Ξ produce, then acceptance tested at that effort; reason: this is what the proof computes on pp.32, 36; the paper names no other solution of the supplier stage
--   - encoding: (1) with the factor Q → profit per unit, for every Ξ ≠ ∅; reason: the proof drops Q on p.32; nothing changes when Q > 0, and (1) is identically 0 when Q = 0
--   - reading: the law of the batches is not specified → independent batches, on the sample space Fin N → Bool with success probability 1 - ρ(e) = √e; reason: (2) multiplies the survival probabilities and the factor 1/|Ξ| on p.38 requires independence
--   - encoding: (8) integrates I(C_k ≥ v₀) over consumers k ∈ [0, 1] → the purchase probability of a generic consumer, given the manufacturer type q; reason: independent signals on a continuum make the integral not literally definable; this is the value the paper assigns to it
--   - reading: (7) conditions on (q̃_k, P) → the expectation conditions on the consumer type and the signal (t, q̃); reason: without t_k the expectation would be v₀ - P for every consumer; the proof on p.31 conditions on (t_k, q̃_k)
--   - encoding: N ∈ ℕ; α ∈ [α̲, ᾱ] with 1/2 < α̲ < ᾱ < 1; suppliers {1, ..., N} → 0 < N; 1/2 < α < 1; suppliers Fin N; reason: the same instances
-- source:
--   Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, proof of Proposition 3.1, p.34

import Mathlib
import Definitions.Def_BlockchainMarketPower_Model

namespace BlockchainMarketPower

/-- Utility without blockchain, Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, proof of Proposition 3.1,
p.34: after any symmetric supplier response, `𝓜_NB = f(P, Ψ; γ)` at a valid order with `|Ξ| = 1` and
`0 < Ψ < P ≤ 2α - 1`, and `𝓜_NB ≤ 0` at every other valid order, including `Ψ ≥ 1`, `|Ξ| ≥ 2` under
any symmetric effort. -/
theorem util_nb {N : ℕ} (p : Params N) (σ : Strategy N) (hσ : σ.SuppliersRespond) (q : Bool)
    (x : Order N) (hx : x.Valid) :
    (x.Ξ.card = 1 ∧ 0 < x.Ψ ∧ x.Ψ < x.P ∧ x.P ≤ 2 * p.α - 1 →
        p.util σ .NB q x = f x.P x.Ψ p.γ) ∧
      (¬ (x.Ξ.card = 1 ∧ 0 < x.Ψ ∧ x.Ψ < x.P ∧ x.P ≤ 2 * p.α - 1) →
        p.util σ .NB q x ≤ 0) := by sorry

end BlockchainMarketPower
