-- Prove2me | Theorems.Thm_DecodablePOMDP_section_4_2_planner_error
-- name    : DecodablePOMDP.section_4_2_planner_error
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:29:12.43632+00:00
-- url     : https://prove2.me/theorems/14274b11-d83a-4bd4-a5cc-1372da7868e4
-- title:
--   §4.2, p.11 — the planner is $2H^2\eta$-optimal in the killed POMDP
-- statement:
--   Under the hypotheses of Theorem 2, let $m_1=(1,\emptyset,e_\perp)$, $\beta_1(s,q)=\mu_1(s)\mathbf 1\{q=\perp\}$ and $\hat\pi$ the planner policy started at $m_1$. Then $m_1\in\mathcal M_1$, $\beta_{m_1}=\beta_1$, and
--
--   $$V^*_L=V^*_1(\beta_1),\qquad V^{\hat\pi}_L=W_1(\beta_1,m_1),\qquad V^*_L-V^{\hat\pi}_L\le2H^2\eta,$$
--
--   for every admissible choice of the planner's free choices.
--
--   This is the planner's guarantee in $\widetilde{\mathcal P}(L)$, obtained from Theorems 2 and 3.
--
--   Differences from the source:
--   - encoding: "initialise the finite planner at time 1 by m₁ = (1, ∅, e_⊥), indicating the history (suffix) at stage 1 is empty, and that no reveal has occurred yet" → explicit clauses m₁ ∈ M₁ and β_{m₁} = β₁; reason: the display uses V*_1(β_{m₁}) and W_1(β_{m₁}, m₁) for V*_1(β₁) and W_1(β₁, m₁)
--   - generalization: the planner (footnote 3: "choose any admissible planner state"; the "last" coordinate of the rounding; a maximiser in (7)) → every admissible choice of these (`IsPlannerChoice`); reason: the paper leaves the choices free; the statement holds for each, so it covers the paper's planner whatever the choice
--   - encoding: fix some 0 < η ≤ 1 (p.10) → hypotheses `0 < η`, `η ≤ 1`, stage h ∈ [1 : H]; reason: the planner's standing assumption and range of stages
--   - generalization: standing assumptions of §3 (ρ ∈ (0, 1], an optimal decoder D_h with (D_h K_h)_{s,s} ≥ ρ, integer L ≥ 1) → any decoder family with d_{h,s} ≥ ρ (`IsRhoDecoderFamily P D ρ`), `0 < ρ ≤ 1`, `1 ≤ L` and `P.IsValid`; reason: the section's standing assumptions (pp.6–8) written as binders; the proofs never use optimality of D_h, so the paper's optimal decoders are a special case
--   - encoding: action space of size A (implicitly A ≥ 1) → `[Nonempty A]`; reason: with no action there is no policy; the paper's A ≥ 1
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), §4.2, p.11

import Mathlib
import Definitions.Def_DecodablePOMDP_Planner

namespace DecodablePOMDP

/-- **§4.2, p.11 — the planner is `2H²η`-optimal in the killed POMDP.** Under the hypotheses of
Theorem 2, with the initial planner state `m₁ = (1, ∅, e_⊥)`, the initial belief
`β₁(s, q) = µ₁(s) 1{q = ⊥}` and the planner policy `π̂` started at `m₁`:
`m₁ ∈ M₁`, `β_{m₁} = β₁`, `V*_L = V*_1(β₁)`, `V^{π̂}_L = W_1(β₁, m₁)`, and
`V*_L − V^{π̂}_L ≤ 2H²η`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §4.2, p.11: "Suppose we initialise the finite
planner at time 1 by m1 = (1, ∅, e⊥), indicating the history (suffix) at stage 1 is empty, and that
no reveal has occurred yet, and let β1(s, q) = µ1(s)1{q = ⊥} be the initial belief. Then
V∗L = V∗1(β1) and V^π̂_L = W1(β1, m1). Hence, the planning and execution error bounds from Theorem 2
and Theorem 3 show that V∗L − V^π̂_L ≤ |V∗1(βm1) − V̂1(m1)| + |V̂1(m1) − W1(βm1, m1)| ≤ 2H²η."

**Formalization Note.** The clauses `m₁ ∈ M₁` and `β_{m₁} = β₁` make explicit what the display
uses ("indicating the history (suffix) at stage 1 is empty, and that no reveal has occurred yet").
The claims on `π̂` hold for every admissible choice of the planner's free choices. -/
theorem section_4_2_planner_error {S A O : Type} [Fintype S] [Fintype A] [Fintype O]
    [DecidableEq S] [DecidableEq A] [Nonempty A] (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ)
    (L : ℕ) (η : ℝ) (hP : P.IsValid) (hD : IsRhoDecoderFamily P D ρ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hL : 1 ≤ L) (hη : 0 < η) (hη1 : η ≤ 1) :
    initState L ∈ plannerStates P D ρ L η 1 ∧
    beliefOf P D ρ L (initState L) = initBelief P L ∧
    optValue (killed P D ρ L) = optValueFrom (killed P D ρ L) 1 (initBelief P L) ∧
    ∀ ch : PlannerChoice S A O L, IsPlannerChoice P D ρ L η ch →
      value (killed P D ρ L) (plannerPolicy P D ρ L η ch (initState L)) =
        execValue P D ρ L η ch 1 (initBelief P L) (initState L) ∧
      optValue (killed P D ρ L) -
          value (killed P D ρ L) (plannerPolicy P D ρ L η ch (initState L)) ≤
        2 * (P.H : ℝ) ^ 2 * η := by sorry

end DecodablePOMDP
