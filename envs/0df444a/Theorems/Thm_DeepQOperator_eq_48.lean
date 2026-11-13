-- Prove2me | Theorems.Thm_DeepQOperator_eq_48
-- name    : DeepQOperator.eq_48
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:03:25.546851+00:00
-- url     : https://prove2.me/theorems/d30972de-a402-4a81-99a6-dd831b5a7478
-- title:
--   (48) and the sign rule: rounded candidate maxima give regret at most $33\varepsilon/128$
-- statement:
--   Let $m\ge2$, $0<\gamma<1$, $\theta\in P_{cb}$, $v\ge1$, and let $J$ satisfy $A_J=A$, $B_J=B$. With $\widetilde\beta_i=Q_v(b_i)$, $\widetilde z_i=Q_v(z_i)$,
--   $$\widetilde A=\max\{1/4,\max_{i\in J}(\widetilde\beta_i+\widetilde z_i/16)\},\quad \widetilde B=\max\{1/4,\max_{i\in J}\widetilde\beta_i\},\quad \widetilde g=\gamma(\widetilde A-\widetilde B-1/32),$$
--   one has
--   $$|\widetilde A-A|\le(1+1/16)2^{-v},\qquad|\widetilde B-B|\le2^{-v},\qquad|\widetilde g-g|\le(33/16)\gamma2^{-v},\tag{48}$$
--   and $(33/16)\gamma2^{-v}\le33\varepsilon/128$ whenever $\varepsilon>0$ and $v\ge\lceil\log_2(8\gamma/\varepsilon)\rceil$. Moreover, for every input and every real estimate $\widetilde g$, choosing $+$ iff $\widetilde g\ge0$ has loss at most $|g-\widetilde g|$.
--
--   This bounds the regret of Theorem 2's protocol on the success event, without a margin assumption.
--
--   Differences from the source:
--   - generalization: "on G" → for every J whose restricted maxima equal A and B; reason: on G the candidate event gives this for the protocol's J
--   - generalization: the sign rule for the protocol's contrasts → for every input θ and every real estimate; reason: it specializes to the protocol's estimate
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix E.3, eq. (48), p.25 (PDF p.28)

import Mathlib
import Definitions.Def_DeepQOperator_Family
import Definitions.Def_DeepQOperator_Quantizer

open Finset

namespace DeepQOperator

/-- **(48) and the sign rule** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix E.3, p.25, PDF p.28).

Let `θ ∈ P_cb`, `v ≥ 1`, and `J` an index set whose restricted maxima (floors kept) equal `A` and `B`.
With `β̃_i = Q_v(b_i)`, `z̃_i = Q_v(z_i)`, `Ã = max{1/4, max_{i∈J}(β̃_i + z̃_i/16)}`,
`B̃ = max{1/4, max_{i∈J} β̃_i}` and `g̃ = γ(Ã - B̃ - 1/32)`:
`|Ã - A| ≤ (1 + 1/16)2^{-v}`, `|B̃ - B| ≤ 2^{-v}`, `|g̃ - g| ≤ (33/16)γ2^{-v}`, and
`(33/16)γ2^{-v} ≤ 33ε/128` whenever `ε > 0` and `v ≥ ⌈log₂(8γ/ε)⌉`. Moreover, for any true and
estimated contrasts, choosing `+` iff the estimate is `≥ 0` has regret at most their absolute
difference.

**Formalization Note.** The hypothesis on `J` is the conclusion of the candidate event (on `G`).
The sign rule is stated for every `θ` and every real estimate `g̃`, with the family's loss (3); the
decision `true` is `+`. -/
theorem eq_48 (m : ℕ) (hm : 2 ≤ m) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (θ : Coord m → ℝ) (hθ : θ ∈ Pcb m) (v : ℕ) (hv : 1 ≤ v) (J : Finset (Fin m))
    (hA : rowAOn m J θ = rowA m θ) (hB : rowBOn m J θ = rowB m θ) :
    |J.fold max (1 / 4 : ℝ) (fun i => qRound v (bScore m i θ) + qRound v (θ (Sum.inr i)) / 16) -
        rowA m θ| ≤ (1 + 1 / 16) * (2 : ℝ) ^ (-(v : ℤ)) ∧
    |J.fold max (1 / 4 : ℝ) (fun i => qRound v (bScore m i θ)) - rowB m θ| ≤ (2 : ℝ) ^ (-(v : ℤ)) ∧
    |γ * (J.fold max (1 / 4 : ℝ) (fun i => qRound v (bScore m i θ) + qRound v (θ (Sum.inr i)) / 16) -
          J.fold max (1 / 4 : ℝ) (fun i => qRound v (bScore m i θ)) - 1 / 32) - contrast m γ θ| ≤
      (33 / 16) * γ * (2 : ℝ) ^ (-(v : ℤ)) ∧
    (∀ ε : ℝ, 0 < ε → ⌈Real.logb 2 (8 * γ / ε)⌉ ≤ (v : ℤ) →
      (33 / 16) * γ * (2 : ℝ) ^ (-(v : ℤ)) ≤ 33 * ε / 128) ∧
    (∀ (θ' : Coord m → ℝ) (gt : ℝ), loss m γ (decide (0 ≤ gt)) θ' ≤ |contrast m γ θ' - gt|) := by sorry

end DeepQOperator
