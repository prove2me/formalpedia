-- Prove2me | Theorems.Thm_BlockchainMarketPower_proposition_3_1_manufacturer
-- name    : BlockchainMarketPower.proposition_3_1_manufacturer
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:27:12.166547+00:00
-- url     : https://prove2.me/theorems/1a2de294-2bff-4d72-a52c-5c9bb5d42ac2
-- title:
--   Proposition 3.1 part 3: the optimal orders (corrected: $\Psi^\star$ unique on $(0,P)$)
-- statement:
--   Consider any strategy in which suppliers play a symmetric effort after every history. An order $(P,\Psi,\Xi)$ is optimal without blockchain if and only if
--
--   $$
--   |\Xi|=1,\qquad P=2\alpha-1,\qquad \Psi\in(0,P),\ \ \Lambda(\Psi,P,1)=0,
--   $$
--
--   and it is optimal with blockchain if and only if
--
--   $$
--   \Xi=S,\qquad P=2(\alpha+\delta(1-\alpha))-1,\qquad \Psi\in(0,P),\ \ \Lambda(\Psi,P,N)=0,
--   $$
--
--   where $S$ is the set of all $N$ suppliers. At an optimal order the utilities are $\mathcal M^\star_{\mathrm{NB}}=f(P,\Psi;\gamma)>0$ and $\mathcal M^\star_{\mathrm B}=f(P,\Psi;\gamma/N)>0$, for either type.
--
--   So the manufacturer sources from a single supplier without blockchain and from all suppliers with it.
--
--   Differences from the source:
--   - correction: Ψ⋆ "is the unique solution" of Λ(Ψ⋆, P, N) = 0 → the root of Λ(·, P, n) in (0, P); reason: Λ is a cubic with several real roots: at α = 3/4, γ = 1/2, N = 1 there is a root in (1, 3) besides the one in (0, 1/2); the proof on pp.35–36 says Ψ∗ ∈ (0, P∗)
--   - generalization: the printed selection (e⋆_NB = 0 for |Ξ| > 1) → every symmetric supplier response after every history; reason: the printed selection is such a response (accepts_nb, effort_b), so the printed claim is a special case
--   - generalization: the equilibrium values are listed → an order is optimal if and only if it has these values, for any symmetric supplier response; reason: both directions; the printed claim is the forward direction
--   - reading: §3.1: accept and effort are simultaneous and (2) depends on the accepting set Γ → symmetric fixed point with exponent |Ξ| - 1, assuming all of Ξ produce, then acceptance tested at that effort; reason: this is what the proof computes on pp.32, 36; the paper names no other solution of the supplier stage
--   - encoding: (1) with the factor Q → profit per unit, for every Ξ ≠ ∅; reason: the proof drops Q on p.32; nothing changes when Q > 0, and (1) is identically 0 when Q = 0
--   - reading: the law of the batches is not specified → independent batches, on the sample space Fin N → Bool with success probability 1 - ρ(e) = √e; reason: (2) multiplies the survival probabilities and the factor 1/|Ξ| on p.38 requires independence
--   - reading: p.15: the price is the same for both types, "we formally establish" → the manufacturer strategy does not depend on the type q and beliefs ignore P; reason: the solution models no type-dependent price or off-path beliefs; the conclusions hold for both types
--   - encoding: (8) integrates I(C_k ≥ v₀) over consumers k ∈ [0, 1] → the purchase probability of a generic consumer, given the manufacturer type q; reason: independent signals on a continuum make the integral not literally definable; this is the value the paper assigns to it
--   - reading: (7) conditions on (q̃_k, P) → the expectation conditions on the consumer type and the signal (t, q̃); reason: without t_k the expectation would be v₀ - P for every consumer; the proof on p.31 conditions on (t_k, q̃_k)
--   - encoding: N ∈ ℕ; α ∈ [α̲, ᾱ] with 1/2 < α̲ < ᾱ < 1; suppliers {1, ..., N} → 0 < N; 1/2 < α < 1; suppliers Fin N; reason: the same instances
-- source:
--   Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, Proposition 3.1 part 3, pp.18–19; proof pp.33–36, 37–39

import Mathlib
import Definitions.Def_BlockchainMarketPower_Model

namespace BlockchainMarketPower

/-- Proposition 3.1 part 3, Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, pp.18–19 (proof pp.33–36,
37–39). After any symmetric supplier response, an order is optimal without blockchain if and only if
`|Ξ| = 1`, `P = 2α - 1` and `Ψ` is the root of `Λ(·, P, 1)` in `(0, P)`; it is optimal with blockchain
if and only if `Ξ` is the set of all suppliers, `P = 2(α + δ(1 - α)) - 1` and `Ψ` is the root of
`Λ(·, P, N)` in `(0, P)`. The optimal utilities are `f(P, Ψ; γ) > 0` and `f(P, Ψ; γ/N) > 0`. -/
theorem proposition_3_1_manufacturer {N : ℕ} (p : Params N) (σ : Strategy N)
    (hσ : σ.SuppliersRespond) (x : Order N) :
    (p.IsOptimalOrder σ .NB x ↔
      x.Ξ.card = 1 ∧ x.P = p.priceStar .NB ∧ IsInteriorRoot p.γ 1 x.P x.Ψ) ∧
    (p.IsOptimalOrder σ .B x ↔
      x.Ξ = Finset.univ ∧ x.P = p.priceStar .B ∧ IsInteriorRoot p.γ N x.P x.Ψ) ∧
    (p.IsOptimalOrder σ .NB x → ∀ q : Bool,
      p.util σ .NB q x = f x.P x.Ψ p.γ ∧ 0 < f x.P x.Ψ p.γ) ∧
    (p.IsOptimalOrder σ .B x → ∀ q : Bool,
      p.util σ .B q x = f x.P x.Ψ (p.γ / (N : ℝ)) ∧ 0 < f x.P x.Ψ (p.γ / (N : ℝ))) := by sorry

end BlockchainMarketPower
