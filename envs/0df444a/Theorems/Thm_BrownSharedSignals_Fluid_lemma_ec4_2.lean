-- Prove2me | Theorems.Thm_BrownSharedSignals_Fluid_lemma_ec4_2
-- name    : BrownSharedSignals.Fluid.lemma_ec4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T01:53:27.48902+00:00
-- url     : https://prove2.me/theorems/efb4d4b4-342e-492a-a466-2975b4c8d7fb
-- title:
--   Lemma EC4.2 — Greedy repair sensitivity
-- statement:
--   Under the Section 6 bounds, fix any local priority ranking and two joint states differing in at most $m$ projects. Couple their admissible proposal vectors so that any project with unchanged local state has the same proposed action. After greedy feasible repair, the number of differing actions is at most
--   $$\left(\frac{b_{\rm upper}}{b_{\rm lower}}+1\right)m+2\frac{b_{\rm upper}}{b_{\rm lower}}.$$
--   The statement holds pointwise for every pair of admissible proposal vectors with this shared-coordinate property. It therefore applies to the paper’s common-randomness fluid proposals. The priority index is local and scanning continues after a rejection.
--
--   Differences from the source:
--   - encoding: periods 1 through T and finite nonempty state and signal sets → periods 0 through T-1 with terminal T, and finite carriers numbered by Fin (size+1); reason: index renaming represents every finite nonempty carrier and changes no model
--   - reading: positive nonzero-action consumptions and the bounded resource ratio invoked in Section 6 → uniform scales satisfy 0 < b_lower <= b_upper; reason: this is the standing positive-scale interpretation required by the printed divisions and bounded ratio; no unit-consumption normalization is imposed
--   - generalization: coupled proposals from the dynamic fluid policy, identical at unchanged local states → all admissible proposal pairs identical at unchanged local states; reason: every source coupling is included; the repair comparison depends only on this shared-coordinate property, not on fluid optimality
-- source:
--   Brown and Zhang (2021), Dynamic Programs with Shared Resources and Signals: Dynamic Fluid Policies and Asymptotic Optimality, DOI https://doi.org/10.1287/opre.2021.2181, supplied July 28, 2021 artifact (published citation basis), Lemma EC4.2, printed EC-13 / PDF 51

import Definitions.Def_BrownSharedSignals_Fluid_GreedyPolicy

open scoped BigOperators
open BrownSharedSignals.Fluid

namespace BrownSharedSignals.Fluid

theorem lemma_ec4_2 {N T : ℕ} (M : Model N T)
    (rlo rhi blo bhi : ℝ) (hb : Bounded M rlo rhi blo bhi) (v : Priority M)
    (t : ℕ) (ht : t < T) (z : Signal M) (s s' : State M) (m : ℕ)
    (hm : stateMismatch M s s' ≤ m)
    (a : Actions M t s z) (a' : Actions M t s' z)
    (hshared : ∀ i, s i = s' i → (a i).val = (a' i).val) :
    mismatch (repair M v t s z (actionVector M a))
      (repair M v t s' z (actionVector M a')) ≤
      (bhi / blo + 1) * (m : ℝ) + 2 * bhi / blo := by sorry

end BrownSharedSignals.Fluid
