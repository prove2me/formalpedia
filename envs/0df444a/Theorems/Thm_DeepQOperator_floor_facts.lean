-- Prove2me | Theorems.Thm_DeepQOperator_floor_facts
-- name    : DeepQOperator.floor_facts
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:03:12.233897+00:00
-- url     : https://prove2.me/theorems/def350f4-d1aa-421b-aaab-26c372c01ed1
-- title:
--   Floor facts: $0\le A-B\le1/16$, $|g|\le\gamma/32$, and indices with $b_i\le3/16$ do not matter
-- statement:
--   Let $m\ge2$, $0<\gamma<1$ and $\theta=(a,z)\in P_{cb}$. Then:
--   1. each $b_i\in[-1/2,1/2]$, and its coefficient vector has $\ell_1$ norm $1/2$;
--   2. $0\le A-B\le1/16$ and $|g|\le\gamma/32$;
--   3. if $b_i\le3/16$ then $b_i+z_i/16\le1/4$;
--   4. hence, for every index set $J$ containing all $i$ with $b_i>3/16$, the maxima restricted to $J$ with their floors kept are exactly $A$ and $B$:
--   $$A_J=A,\qquad B_J=B.$$
--
--   These facts bound the regret of any decision by $\gamma/32$ and show that only indices with large Walsh score affect the decision.
--
--   **Formalization Note** $g$ is computed from the scores (1) as $t_+-t_-$.
--
--   Differences from the source:
--   - reading: "this index cannot raise either maximum above its known floor. A tie at the floor cannot change the score" → for every J containing {i : b_i > 3/16}, A_J = A and B_J = B; reason: the form in which Appendix E.3 uses the sentence; it covers ties at the floor
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix E.2, p.23 (PDF p.26); = (36), Appendix D.1, p.20

import Mathlib
import Definitions.Def_DeepQOperator_Family

open Finset

namespace DeepQOperator

/-- **Floor facts** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix E.2, p.23, PDF p.26; = (36) of Appendix D.1, p.20).

On the full box `P_cb`: each `b_i ∈ [-1/2, 1/2]` with coefficient `ℓ₁` norm `1/2`; `0 ≤ A - B ≤ 1/16`
and `|g| ≤ γ/32`; if `b_i ≤ 3/16` then `b_i + z_i/16 ≤ 1/4`; hence for every index set `J` containing
all `i` with `b_i > 3/16`, the maxima restricted to `J` with the floors kept are exactly `A` and `B`
("this index cannot raise either maximum above its known floor. A tie at the floor cannot change the
score").

**Formalization Note.** `g` is `contrast m γ θ = t₊ - t₋` computed from (1). The coefficient
vector of `b_i` is that of the raw site `siteB m i`. The last clause is the form in which E.3 uses the
floor sentence. -/
theorem floor_facts (m : ℕ) (hm : 2 ≤ m) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (θ : Coord m → ℝ) (hθ : θ ∈ Pcb m) :
    (∀ i : Fin m, bScore m i θ ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2) ∧
      ∑ c : Coord m, |(siteB m i).1 c| = 1 / 2) ∧
    0 ≤ rowA m θ - rowB m θ ∧ rowA m θ - rowB m θ ≤ 1 / 16 ∧
    |contrast m γ θ| ≤ γ / 32 ∧
    (∀ i : Fin m, bScore m i θ ≤ 3 / 16 → bScore m i θ + θ (Sum.inr i) / 16 ≤ 1 / 4) ∧
    (∀ J : Finset (Fin m), (∀ i, 3 / 16 < bScore m i θ → i ∈ J) →
      rowAOn m J θ = rowA m θ ∧ rowBOn m J θ = rowB m θ) := by sorry

end DeepQOperator
