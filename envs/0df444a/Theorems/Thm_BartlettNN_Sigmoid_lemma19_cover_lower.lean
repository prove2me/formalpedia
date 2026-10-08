-- Prove2me | Theorems.Thm_BartlettNN_Sigmoid_lemma19_cover_lower
-- name    : BartlettNN.Sigmoid.lemma19_cover_lower
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:39:00.918967+00:00
-- url     : https://prove2.me/theorems/0a012ee5-4fa4-4ea0-b574-47e3bc8d477f
-- title:
--   Lemma 19 — fat-shattering lower-bounds ℓ1 covering numbers
-- statement:
--   Let $F$ be a class of $[0,1]$-valued functions. If $\operatorname{fat}_F(4\gamma)\ge d$, then
--
--   $$\log_2 N_1(F,\gamma,d)\ge d/32.$$
--
--   The covering number is evaluated on a sample of length $d$. The statement gives the finite-cover reading: for every finite upper bound $N\ge N_1(F,\gamma,d)$, one has $\log_2N\ge d/32$. If no finite cover exists, the original lower bound holds automatically in the extended sense. This is the capacity-to-covering step used by the network bounds.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), p. 532, Lemma 19 [6]; https://doi.org/10.1109/18.661502

import Mathlib
import Definitions.Def_BartlettNN_Sigmoid_Fat
import Definitions.Def_BartlettNN_FatNet_coverNum

namespace BartlettNN.Sigmoid

/-- Lemma 19 [6], p. 532: BartlettNN.Margin.fat-shattering forces a lower bound on the sample ℓ1 cover. -/
theorem lemma19_cover_lower :
    ∀ {X : Type} (F : Set (X → ℝ)) (γ : ℝ) (d : ℕ),
      (∀ f ∈ F, ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
      (d : ℕ∞) ≤ BartlettNN.Margin.fat F (4 * γ) →
      ∀ N : ℕ, BartlettNN.FatNet.N1 F γ d ≤ N → (d : ℝ) / 32 ≤ Real.logb 2 N := by sorry

end BartlettNN.Sigmoid
