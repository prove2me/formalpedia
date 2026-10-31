-- Prove2me | Theorems.Thm_BlockchainMarketPower_proposition_4_1
-- name    : BlockchainMarketPower.proposition_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:27:12.230692+00:00
-- url     : https://prove2.me/theorems/c7b0a757-37de-4388-af76-c667940adc5a
-- title:
--   Proposition 4.1: $\Omega^\star>0$, and all parties adopt whenever $0<\chi\le\Omega^\star$
-- statement:
--   There is a number $\Omega^\star>0$, not depending on the implementation cost, such that for every cost $\chi>0$:
--
--   1. an equilibrium exists;
--   2. in every equilibrium, the manufacturer's incremental welfare from blockchain adoption is $\Omega^\star$, for either manufacturer type;
--   3. in every equilibrium, blockchain is adopted if and only if $\chi\le\Omega^\star$;
--   4. in every equilibrium with $\chi\le\Omega^\star$, every supplier receives the manufacturer's order under blockchain and accepts it.
--
--   In particular, blockchain adoption arises in equilibrium for the manufacturer and all suppliers whenever $0<\chi\le\Omega^\star$. Here equilibrium means the symmetric subgame perfect equilibrium of the model: the supplier effort is a best response after every order, on and off the path, and the manufacturer's order maximizes the mean-variance utility over all orders.
--
--   This is the main result of the paper: when the manufacturer has market power, the gains from blockchain are not competed away.
--
--   **Formalization Note** The theorem makes no use of Assumption 1, and it covers $N=1$ and $\delta=1$. The number $\Omega^\star$ is quantified before $\chi$.
--
--   Differences from the source:
--   - generalization: the printed effort selection → every symmetric supplier response at every order; reason: the printed selection is one of them (accepts_nb, effort_b), so the printed equilibrium is included
--   - generalization: "if" χ ≤ Ω⋆, adoption arises → adoption if and only if χ ≤ Ω⋆; reason: this is Proposition 3.1 part 4; the printed direction is a special case
--   - encoding: "blockchain adoption arises in equilibrium" → existence of an equilibrium for every χ > 0, and the claims for every equilibrium; Ω⋆ quantified before χ; reason: makes existence explicit and keeps the paper's "Ω⋆ does not depend on the implementation cost", p.19
--   - reading: the supplier stage of §3.1 → symmetric fixed point assuming all of Ξ produce, then acceptance tested at that effort; reason: this is what the proof computes on pp.32, 36; the paper names no other solution of the supplier stage
--   - encoding: (1) with the factor Q → profit per unit, for every Ξ ≠ ∅; reason: the proof drops Q on p.32; nothing changes when Q > 0, and (1) is identically 0 when Q = 0
--   - reading: the law of the batches is not specified → independent batches, on the sample space Fin N → Bool with success probability 1 - ρ(e) = √e; reason: (2) multiplies the survival probabilities and the factor 1/|Ξ| on p.38 requires independence
--   - reading: p.15: the price is the same for both types, "we formally establish" → the manufacturer strategy does not depend on the type q and beliefs ignore P; reason: the solution models no type-dependent price or off-path beliefs; the conclusions hold for both types
--   - encoding: (8) integrates I(C_k ≥ v₀) over consumers k ∈ [0, 1] → the purchase probability of a generic consumer, given the manufacturer type q; reason: independent signals on a continuum make the integral not literally definable; this is the value the paper assigns to it
--   - reading: (7) conditions on (q̃_k, P) → the expectation conditions on the consumer type and the signal (t, q̃); reason: without t_k the expectation would be v₀ - P for every consumer; the proof on p.31 conditions on (t_k, q̃_k)
--   - encoding: N ∈ ℕ; α ∈ [α̲, ᾱ] with 1/2 < α̲ < ᾱ < 1; suppliers {1, ..., N} → 0 < N; 1/2 < α < 1; suppliers Fin N; reason: the same instances
-- source:
--   Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, Proposition 4.1, p.19 (runs on to p.20); proof p.40

import Mathlib
import Definitions.Def_BlockchainMarketPower_Model

namespace BlockchainMarketPower

/-- Proposition 4.1 (Blockchain Adoption in Equilibrium), Iyengar–Saleh–Sethuraman–Wang,
SSRN 3950580, p.19 (runs on to p.20; proof p.40). There is `Ω⋆ > 0`, fixed before the cost `χ`, such that
for every `χ > 0` an equilibrium exists and in every equilibrium: the incremental welfare is `Ω⋆` for
both manufacturer types; blockchain is adopted if and only if `χ ≤ Ω⋆`; and when `χ ≤ Ω⋆`, every supplier
receives the blockchain order and accepts it.

**Formalization Note.** The equilibrium quantifies over every symmetric supplier response at every order,
which contains the printed one. `Ω⋆` precedes `χ`: this is the paper's "`Ω⋆` does not depend on the
implementation cost", p.19. -/
theorem proposition_4_1 {N : ℕ} (p : Params N) :
    ∃ Ωstar : ℝ, 0 < Ωstar ∧ ∀ χ : ℝ, 0 < χ →
      (∃ σ : Strategy N, p.IsSPNE χ σ) ∧
      ∀ σ : Strategy N, p.IsSPNE χ σ →
        (∀ q : Bool, p.Omega σ q = Ωstar) ∧
        (σ.adopt ↔ χ ≤ Ωstar) ∧
        (χ ≤ Ωstar →
          (σ.order .B).Ξ = Finset.univ ∧ ∀ j : Fin N, j ∈ σ.accepted .B (σ.order .B)) := by sorry

end BlockchainMarketPower
