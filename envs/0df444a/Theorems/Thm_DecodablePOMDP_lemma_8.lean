-- Prove2me | Theorems.Thm_DecodablePOMDP_lemma_8
-- name    : DecodablePOMDP.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:26:55.140042+00:00
-- url     : https://prove2.me/theorems/af69fc8f-daf9-49b8-a504-4c231f5ebde6
-- title:
--   Lemma 8 — values are $H$-Lipschitz in the belief
-- statement:
--   Let $\mathcal P$ be a valid POMDP, $\rho\in(0,1]$, $D_h$ decoders with $d_{h,s}\ge\rho$, $L\ge1$ and $h\ge1$ a stage. For every randomised policy $\pi$ of $\widetilde{\mathcal P}(L)$ acting from stage $h$ and all beliefs $\beta,\beta'$ on the states of $\widetilde{\mathcal P}(L)$,
--
--   $$|V^\pi_h(\beta)-V^\pi_h(\beta')|\le H\,\|\beta-\beta'\|_1,\tag{15}$$
--
--   and the same bound holds for the optimal value $V^*_h$.
--
--   Together with Lemma 7 this controls the effect of rounding on the planner's values.
--
--   Differences from the source:
--   - encoding: "two beliefs over the augmented hidden states"; "a policy" → probability vectors on the states (S × Q) ∪ {∂} of P̃(L); randomised policies of P̃(L) acting on histories after stage h; reason: the lemma is applied to P̃(L) in A.7–A.8
--   - generalization: standing assumptions of §3 (ρ ∈ (0, 1], an optimal decoder D_h with (D_h K_h)_{s,s} ≥ ρ, integer L ≥ 1) → any decoder family with d_{h,s} ≥ ρ (`IsRhoDecoderFamily P D ρ`), `0 < ρ ≤ 1`, `1 ≤ L` and `P.IsValid`; reason: the section's standing assumptions (pp.6–8) written as binders; the proofs never use optimality of D_h, so the paper's optimal decoders are a special case
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), Lemma 8, p.18

import Mathlib
import Definitions.Def_DecodablePOMDP_Killed

namespace DecodablePOMDP

open CalibratedCE.Forecast

/-- **Lemma 8 — values are `H`-Lipschitz in the belief.** Let `P` be a valid POMDP, `ρ ∈ (0, 1]`,
`D_h` decoders with `d_{h,s} ≥ ρ`, `L ≥ 1`, and `h ≥ 1` a stage. For every randomised policy `π`
of `P̃(L)` (acting from stage `h`) and all beliefs `β, β′` on the killed states,
`|V^π_h(β) − V^π_h(β′)| ≤ H ‖β − β′‖₁`, and the same holds for the optimal value `V*_h`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), Lemma 8, p.18: "Let h be a stage and π be a
policy, and let β, β′ be two beliefs over the augmented hidden states. Then
|V^π_h(β) − V^π_h(β′)| ≤ H∥β − β′∥1. (15) The same Lipschitz condition holds for the optimal value
V∗_h."

**Formalization Note.** `V^π_h(β)` is the expected reward from time `h + 1` to `H` in `P̃(L)` from
hidden law `β` at stage `h`; beliefs are probability vectors on `(S × Q) ∪ {∂}`. -/
theorem lemma_8 {S A O : Type} [Fintype S] [Fintype A] [Fintype O] [DecidableEq S]
    (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) (L : ℕ) (hP : P.IsValid)
    (hD : IsRhoDecoderFamily P D ρ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 1 ≤ L)
    (h : ℕ) (hh1 : 1 ≤ h) (β β' : Option (S × Option (Fin L)) → ℝ) (hβ : IsDist β)
    (hβ' : IsDist β') :
    (∀ π : PolicyFn A (Option (O × S)), IsRandPolicy π →
      |valueFrom (killed P D ρ L) h β π - valueFrom (killed P D ρ L) h β' π| ≤
        (P.H : ℝ) * ∑ ξ, |β ξ - β' ξ|) ∧
    |optValueFrom (killed P D ρ L) h β - optValueFrom (killed P D ρ L) h β'| ≤
        (P.H : ℝ) * ∑ ξ, |β ξ - β' ξ| := by sorry

end DecodablePOMDP
