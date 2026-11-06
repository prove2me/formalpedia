-- Prove2me | Theorems.Thm_DecodablePOMDP_theorem_3
-- name    : DecodablePOMDP.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:29:00.652673+00:00
-- url     : https://prove2.me/theorems/98d82b4b-1a81-4387-b36b-8afab9769f9c
-- title:
--   Theorem 3 — execution error $E^{\mathrm{exec}}_h\le H^2\eta$
-- statement:
--   Under the hypotheses of Theorem 2, for every stage $h\in[1:H]$ and every finite planner state $m\in\mathcal M_h$,
--
--   $$\big|W_h(\beta_m,m)-\widehat V_h(m)\big|\le H^2\eta,$$
--
--   where $W_h(\beta,m)$ is the expected cumulative reward of $\widetilde{\mathcal P}(L)$ from time $h+1$ to $H$ when the hidden state law at stage $h$ is $\beta$ and the finite planner (actions $\hat a$, memory updates $m^+$) starts in state $m$. That is, $E^{\mathrm{exec}}_h\le H^2\eta$.
--
--   The reward the planner actually collects is close to the value recorded in its table.
--
--   Differences from the source:
--   - encoding: E_h := max_{m∈M_h} |…| ≤ H²η → |…| ≤ H²η for every m ∈ M_h; reason: equivalent for the finite set M_h, and meaningful when M_h = ∅
--   - generalization: the planner (footnote 3: "choose any admissible planner state"; the "last" coordinate of the rounding; a maximiser in (7)) → every admissible choice of these (`IsPlannerChoice`); reason: the paper leaves the choices free; the statement holds for each, so it covers the paper's planner whatever the choice
--   - encoding: fix some 0 < η ≤ 1 (p.10) → hypotheses `0 < η`, `η ≤ 1`, stage h ∈ [1 : H]; reason: the planner's standing assumption and range of stages
--   - generalization: standing assumptions of §3 (ρ ∈ (0, 1], an optimal decoder D_h with (D_h K_h)_{s,s} ≥ ρ, integer L ≥ 1) → any decoder family with d_{h,s} ≥ ρ (`IsRhoDecoderFamily P D ρ`), `0 < ρ ≤ 1`, `1 ≤ L` and `P.IsValid`; reason: the section's standing assumptions (pp.6–8) written as binders; the proofs never use optimality of D_h, so the paper's optimal decoders are a special case
--   - encoding: action space of size A (implicitly A ≥ 1) → `[Nonempty A]`; reason: with no action there is no policy; the paper's A ≥ 1
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), Theorem 3, p.11 (proof A.8, p.19)

import Mathlib
import Definitions.Def_DecodablePOMDP_Planner

namespace DecodablePOMDP

/-- **Theorem 3 — execution error.** Under the hypotheses of Theorem 2, for every stage
`h ∈ [1 : H]` and every finite planner state `m ∈ M_h`,
`|W_h(β_m, m) − V̂_h(m)| ≤ H²η`, where `W_h(β, m)` is the expected cumulative reward of `P̃(L)` from
time `h + 1` to `H` when the hidden state law at stage `h` is `β` and the finite planner (actions
`â`, memory updates `m⁺`) starts in state `m`; that is, `E^exec_h ≤ H²η`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), Theorem 3, p.11: "Let
E^exec_h := max_{m∈Mh} |Wh(βm, m) − V̂h(m)| where Wh(β, m) is the expected cumulative reward from time
h + 1 to H, when the hidden state distribution is β and the finite planner has state m. Then for
every time h, E^exec_h ≤ H²η."

**Formalization Note.** Stated pointwise for every `m ∈ M_h`, and for every admissible choice of
the planner (`IsPlannerChoice`): any maximiser `â` of (7), any fallback state of footnote 3, any
coordinate receiving the remaining mass in the rounding of A.6. -/
theorem theorem_3 {S A O : Type} [Fintype S] [Fintype A] [Fintype O] [DecidableEq S]
    [DecidableEq A] [Nonempty A] (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) (L : ℕ) (η : ℝ)
    (hP : P.IsValid) (hD : IsRhoDecoderFamily P D ρ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 1 ≤ L)
    (hη : 0 < η) (hη1 : η ≤ 1) (ch : PlannerChoice S A O L) (hch : IsPlannerChoice P D ρ L η ch) :
    ∀ h, 1 ≤ h → h ≤ P.H → ∀ m ∈ plannerStates P D ρ L η h,
      |execValue P D ρ L η ch h (beliefOf P D ρ L m) m - Vhat P D ρ L η ch m| ≤
        (P.H : ℝ) ^ 2 * η := by sorry

end DecodablePOMDP
