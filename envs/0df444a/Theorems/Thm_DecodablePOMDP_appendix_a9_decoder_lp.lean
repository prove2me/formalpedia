-- Prove2me | Theorems.Thm_DecodablePOMDP_appendix_a9_decoder_lp
-- name    : DecodablePOMDP.appendix_a9_decoder_lp
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:24:59.756693+00:00
-- url     : https://prove2.me/theorems/91200d13-9a77-49d8-a98c-607fede2be38
-- title:
--   App. A.9, p.20, (17) — $\rho(K)$ is the optimal value of a linear program
-- statement:
--   Let $K$ be an observation channel from a nonempty finite state set $\mathcal S$ to a finite set $\mathcal O$. Then
--
--   1. the maximum in $\rho(K)=\max_{D\in\mathcal D}\min_s\sum_yK(y\mid s)D(s\mid y)$ is attained by some decoder $D^*$;
--   2. $\rho(K)$ is the optimal value of the linear program
--   $$\max\ \rho\quad\text{s.t.}\quad\sum_yK(y\mid s)D(s\mid y)\ge\rho\ \ \forall s,\qquad\sum_sD(s\mid y)=1\ \ \forall y,\qquad D(s\mid y)\ge0;\tag{17}$$
--   3. for $\rho\in(0,1]$, $K$ is $\rho$-decodable if and only if $\rho\le\rho(K)$.
--
--   An optimal decoder, and the best decodability constant, are thus computable by linear programming.
--
--   Differences from the source:
--   - generalization: "ρ(K) is the optimal value of the linear program (17)" → plus attainment of the max defining ρ(K) and the equivalence with Definition 3; reason: attainment is implicit in the printed "max"; the equivalence links ρ(K) to ρ-decodability as the paper uses it (p.5)
--   - encoding: K ∈ ℝ^{O×S} an observation kernel on a state space of size S → each row K(· | s) a probability vector (`IsDist`) and `[Nonempty S]`; reason: an observation kernel is a channel (Definition 1) and the state space has S ≥ 1 states; with S empty the min over states is undefined
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), App. A.9, p.20, (17)

import Mathlib
import Definitions.Def_DecodablePOMDP_OptDecodability
import Definitions.Def_DecodablePOMDP_IsDecodable

namespace DecodablePOMDP

open CalibratedCE.Forecast

/-- **App. A.9, p.20, (17) — the optimal decodability constant is the value of a linear program.**
Let `K` be an observation channel from a nonempty finite `S` to a finite `O` (each `K(· | s)` a
probability vector). Then
1. the maximum defining `ρ(K) = max_D min_s Σ_y K(y | s) D(s | y)` is attained by a decoder `D*`;
2. `ρ(K)` is the optimal value of the linear program (17): it is the greatest `ρ` for which some
   column-stochastic `D` satisfies `Σ_y K(y | s) D(s | y) ≥ ρ` for all `s`;
3. for `ρ ∈ (0, 1]`, `K` is ρ-decodable if and only if `ρ ≤ ρ(K)`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), App. A.9, p.20: "Then ρ(K) is the optimal
value of the following linear program: max ρ subject to Σ_y K(y | s)D(s | y) ≥ ρ for all s,
Σ_s D(s | y) = 1 for all y, D(s | y) ≥ 0 for all s, y. (17)"

**Formalization Note.** Clauses 1 and 3 make explicit the attainment implicit in "max" (p.20) and
the link to Definition 3; the polynomial-time solvability of (17) is part of the goal's time
bound, not of this item. -/
theorem appendix_a9_decoder_lp {S O : Type} [Fintype S] [Fintype O] [Nonempty S]
    (Kc : S → O → ℝ) (hK : ∀ s, IsDist (Kc s)) :
    (∃ Dstar : O → S → ℝ, (∀ y, IsDist (Dstar y)) ∧
      ⨅ s, ∑ y, Kc s y * Dstar y s = optDecodability Kc) ∧
    IsGreatest {r : ℝ | ∃ D : O → S → ℝ, (∀ y, IsDist (D y)) ∧ ∀ s, r ≤ ∑ y, Kc s y * D y s}
      (optDecodability Kc) ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → (ChannelDecodable Kc ρ ↔ ρ ≤ optDecodability Kc) := by sorry

end DecodablePOMDP
