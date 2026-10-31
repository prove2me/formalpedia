-- Prove2me | Theorems.Thm_BlockchainMarketPower_proposition_3_1
-- name    : BlockchainMarketPower.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:27:23.523148+00:00
-- url     : https://prove2.me/theorems/2f536159-29d2-451e-a2e8-f51c415901cf
-- title:
--   Proposition 3.1: existence and the adoption rule (corrected: $\Psi^\star$ unique on $(0,P)$)
-- statement:
--   Let $\chi>0$. An equilibrium exists, and it can be chosen so that suppliers play the printed efforts $e^\star_{\mathrm{NB}}$, $e^\star_{\mathrm{B}}$ after every history. In every equilibrium, with $P^\star_{\mathrm{NB}}=2\alpha-1$, $P^\star_{\mathrm B}=2(\alpha+\delta(1-\alpha))-1$ and $\Psi^\star_{\mathrm{NB}},\Psi^\star_{\mathrm B}$ the roots of $\Lambda(\cdot,P^\star_{\mathrm{NB}},1)$ and $\Lambda(\cdot,P^\star_{\mathrm B},N)$ in the respective intervals $(0,P^\star)$, the incremental welfare is
--
--   $$
--   \Omega^\star=f\bigl(P^\star_{\mathrm B},\Psi^\star_{\mathrm B};\tfrac{\gamma}{N}\bigr)-f\bigl(P^\star_{\mathrm{NB}},\Psi^\star_{\mathrm{NB}};\gamma\bigr)
--   $$
--
--   for either manufacturer type, and blockchain is adopted if and only if $\Omega^\star\ge\chi$.
--
--   This closes the backward induction: the adoption decision is a comparison of $\chi$ with an explicit number that does not depend on $\chi$.
--
--   Differences from the source:
--   - correction: Ψ⋆ "is the unique solution" of Λ(Ψ⋆, P, N) = 0 → the root of Λ(·, P, n) in (0, P); reason: Λ is a cubic with several real roots: at α = 3/4, γ = 1/2, N = 1 there is a root in (1, 3) besides the one in (0, 1/2); the proof on pp.35–36 says Ψ∗ ∈ (0, P∗)
--   - generalization: the printed selection (e⋆_NB = 0 for |Ξ| > 1) → every symmetric supplier response after every history; reason: the printed selection is such a response (accepts_nb, effort_b), so the printed claim is a special case
--   - encoding: "The symmetric equilibrium for the model is defined as follows" → existence of an SPNE is stated, with the printed efforts as one selection; reason: makes existence explicit and rules out a vacuous statement
--   - reading: §3.1: accept and effort are simultaneous and (2) depends on the accepting set Γ → symmetric fixed point with exponent |Ξ| - 1, assuming all of Ξ produce, then acceptance tested at that effort; reason: this is what the proof computes on pp.32, 36; the paper names no other solution of the supplier stage
--   - encoding: (1) with the factor Q → profit per unit, for every Ξ ≠ ∅; reason: the proof drops Q on p.32; nothing changes when Q > 0, and (1) is identically 0 when Q = 0
--   - reading: the law of the batches is not specified → independent batches, on the sample space Fin N → Bool with success probability 1 - ρ(e) = √e; reason: (2) multiplies the survival probabilities and the factor 1/|Ξ| on p.38 requires independence
--   - reading: p.15: the price is the same for both types, "we formally establish" → the manufacturer strategy does not depend on the type q and beliefs ignore P; reason: the solution models no type-dependent price or off-path beliefs; the conclusions hold for both types
--   - encoding: (8) integrates I(C_k ≥ v₀) over consumers k ∈ [0, 1] → the purchase probability of a generic consumer, given the manufacturer type q; reason: independent signals on a continuum make the integral not literally definable; this is the value the paper assigns to it
--   - reading: (7) conditions on (q̃_k, P) → the expectation conditions on the consumer type and the signal (t, q̃); reason: without t_k the expectation would be v₀ - P for every consumer; the proof on p.31 conditions on (t_k, q̃_k)
--   - encoding: N ∈ ℕ; α ∈ [α̲, ᾱ] with 1/2 < α̲ < ᾱ < 1; suppliers {1, ..., N} → 0 < N; 1/2 < α < 1; suppliers Fin N; reason: the same instances
-- source:
--   Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, Proposition 3.1, pp.17–19, part 4, p.19; proof pp.39–40

import Mathlib
import Definitions.Def_BlockchainMarketPower_Model

namespace BlockchainMarketPower

/-- Proposition 3.1, Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, pp.17–19, with part 4 (adoption), p.19,
proof pp.39–40. For every cost `χ > 0` an equilibrium exists, and one of them plays the printed efforts
after every history. In every equilibrium `Ω = f(P⋆_B, Ψ⋆_B; γ/N) - f(P⋆_NB, Ψ⋆_NB; γ)` for both
manufacturer types, and blockchain is adopted if and only if `χ` does not exceed this value. -/
theorem proposition_3_1 {N : ℕ} (p : Params N) (χ : ℝ) (hχ : 0 < χ) :
    (∃ σ : Strategy N, p.IsSPNE χ σ ∧
      ∀ (r : Regime) (P Ψ : ℝ) (Ξ : Finset (Fin N)), 0 ≤ P → 0 ≤ Ψ → Ξ.Nonempty →
        σ.effort r P Ψ Ξ = printedEffort r Ξ.card Ψ) ∧
    ∀ σ : Strategy N, p.IsSPNE χ σ → ∀ ΨNB ΨB : ℝ,
      IsInteriorRoot p.γ 1 (p.priceStar .NB) ΨNB →
      IsInteriorRoot p.γ N (p.priceStar .B) ΨB →
      (∀ q : Bool, p.Omega σ q =
        f (p.priceStar .B) ΨB (p.γ / (N : ℝ)) - f (p.priceStar .NB) ΨNB p.γ) ∧
      (σ.adopt ↔
        χ ≤ f (p.priceStar .B) ΨB (p.γ / (N : ℝ)) - f (p.priceStar .NB) ΨNB p.γ) := by sorry

end BlockchainMarketPower
