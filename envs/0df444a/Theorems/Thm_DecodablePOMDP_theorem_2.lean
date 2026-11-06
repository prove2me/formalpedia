-- Prove2me | Theorems.Thm_DecodablePOMDP_theorem_2
-- name    : DecodablePOMDP.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:29:26.168236+00:00
-- url     : https://prove2.me/theorems/d378d943-7c4c-4028-95ac-d07232c44357
-- title:
--   Theorem 2 — planning error $E^{\mathrm{plan}}_h\le H^2\eta$
-- statement:
--   Let $\mathcal P$ be a valid POMDP with a nonempty action set, $\rho\in(0,1]$, $D_h$ decoders with $d_{h,s}\ge\rho$, $L\ge1$ and $0<\eta\le1$, and fix any admissible choice of the planner's free choices. For every stage $h\in[1:H]$ and every finite planner state $m\in\mathcal M_h$,
--
--   $$\big|V^*_h(\beta_m)-\widehat V_h(m)\big|\le H^2\eta,$$
--
--   i.e. the planning error $E^{\mathrm{plan}}_h=\max_{m\in\mathcal M_h}|V^*_h(\beta_m)-\widehat V_h(m)|$ is at most $H^2\eta$. Here $V^*_h$ is the optimal value to go of $\widetilde{\mathcal P}(L)$ and $\widehat V_h$ the table (6).
--
--   The table computed on the finite grid thus approximates the true optimal values of the killed POMDP.
--
--   Differences from the source:
--   - encoding: E_h := max_{m∈M_h} |…| ≤ H²η → |…| ≤ H²η for every m ∈ M_h; reason: equivalent for the finite set M_h, and meaningful when M_h = ∅
--   - generalization: the planner (footnote 3: "choose any admissible planner state"; the "last" coordinate of the rounding; a maximiser in (7)) → every admissible choice of these (`IsPlannerChoice`); reason: the paper leaves the choices free; the statement holds for each, so it covers the paper's planner whatever the choice
--   - encoding: fix some 0 < η ≤ 1 (p.10) → hypotheses `0 < η`, `η ≤ 1`, stage h ∈ [1 : H]; reason: the planner's standing assumption and range of stages
--   - generalization: standing assumptions of §3 (ρ ∈ (0, 1], an optimal decoder D_h with (D_h K_h)_{s,s} ≥ ρ, integer L ≥ 1) → any decoder family with d_{h,s} ≥ ρ (`IsRhoDecoderFamily P D ρ`), `0 < ρ ≤ 1`, `1 ≤ L` and `P.IsValid`; reason: the section's standing assumptions (pp.6–8) written as binders; the proofs never use optimality of D_h, so the paper's optimal decoders are a special case
--   - encoding: action space of size A (implicitly A ≥ 1) → `[Nonempty A]`; reason: with no action there is no policy; the paper's A ≥ 1
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), Theorem 2, p.11 (proof A.7, pp.17–19)

import Mathlib
import Definitions.Def_DecodablePOMDP_Planner

namespace DecodablePOMDP

/-- **Theorem 2 — planning error.** Let `P` be a valid POMDP with a nonempty action set,
`ρ ∈ (0, 1]`, `D_h` decoders with `d_{h,s} ≥ ρ`, `L ≥ 1` and `0 < η ≤ 1`. For every stage
`h ∈ [1 : H]` and every finite planner state `m ∈ M_h`,
`|V*_h(β_m) − V̂_h(m)| ≤ H²η`; that is, `E^plan_h := max_{m∈M_h} |V*_h(β_m) − V̂_h(m)| ≤ H²η`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), Theorem 2, p.11: "Define
E^plan_h := max_{m∈Mh} |V∗_h(βm) − V̂h(m)| to be the planning error. Then for each time h,
E^plan_h ≤ H²η."

**Formalization Note.** The maximum over the finite set `M_h` is stated pointwise for every
`m ∈ M_h` (equivalent, and meaningful also if `M_h = ∅`). `V*_h(β)` is the optimal value to go of
`P̃(L)` from belief `β` at stage `h`; `V̂` is the table (6) with the planner successor `m⁺`. The
planner's free choices (footnote 3's fallback state, the coordinate receiving the remaining mass in
the rounding of A.6) are arbitrary admissible ones (`IsPlannerChoice`). -/
theorem theorem_2 {S A O : Type} [Fintype S] [Fintype A] [Fintype O] [DecidableEq S]
    [Nonempty A] (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) (L : ℕ) (η : ℝ)
    (hP : P.IsValid) (hD : IsRhoDecoderFamily P D ρ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 1 ≤ L)
    (hη : 0 < η) (hη1 : η ≤ 1) (ch : PlannerChoice S A O L) (hch : IsPlannerChoice P D ρ L η ch) :
    ∀ h, 1 ≤ h → h ≤ P.H → ∀ m ∈ plannerStates P D ρ L η h,
      |optValueFrom (killed P D ρ L) h (beliefOf P D ρ L m) - Vhat P D ρ L η ch m| ≤
        (P.H : ℝ) ^ 2 * η := by sorry

end DecodablePOMDP
