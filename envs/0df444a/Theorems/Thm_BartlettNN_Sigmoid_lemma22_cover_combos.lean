-- Prove2me | Theorems.Thm_BartlettNN_Sigmoid_lemma22_cover_combos
-- name    : BartlettNN.Sigmoid.lemma22_cover_combos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:15:32.59534+00:00
-- url     : https://prove2.me/theorems/3551d9f0-de33-4262-89a2-6b33b6770357
-- title:
--   Lemma 22 — ℓ2 cover of bounded-weight combinations
-- statement:
--   Let $F$ be a nonempty class of functions valued in $[-M/2,M/2]$, with $M>0$, and let $H=\operatorname{combos}(F,A)$ for $A>0$. For $\gamma>0$ and a nonempty sample length $m$,
--
--   $$\log_2 N_2(H,\gamma,m)\le \frac{2M^2A^2}{\gamma^2}\log_2\!\left(2N_2\!\left(F,\frac{\gamma}{2A},m\right)+1\right).$$
--
--   In the formal statement a finite upper bound for the right-hand covering number yields a finite covering number on the left with this inequality. An infinite right-hand covering number makes the printed upper bound vacuous. The result controls arbitrary finite-width combinations with one covering number for their unit class.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), p. 532, Lemma 22; https://doi.org/10.1109/18.661502

import Mathlib
import Definitions.Def_BartlettNN_FatNet_coverNum
import Definitions.Def_BartlettNN_Sigmoid_Networks

namespace BartlettNN.Sigmoid

/-- Lemma 22, p. 532: covering an ℓ1-bounded combination class from a cover of its units. -/
theorem lemma22_cover_combos :
    ∀ {X : Type} (F : Set (X → ℝ)) (M A γ : ℝ) (m : ℕ),
      F.Nonempty →
      (∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-M / 2) (M / 2)) →
      0 < M → 0 < A → 0 < γ → 1 ≤ m →
      ∀ N : ℕ, BartlettNN.FatNet.N2 F (γ / (2 * A)) m ≤ N →
        ∃ K : ℕ, BartlettNN.FatNet.N2 (BartlettNN.FatNet.combos F A) γ m = K ∧
          Real.logb 2 K ≤ (2 * M ^ 2 * A ^ 2 / γ ^ 2) * Real.logb 2 (2 * N + 1) := by sorry

end BartlettNN.Sigmoid
