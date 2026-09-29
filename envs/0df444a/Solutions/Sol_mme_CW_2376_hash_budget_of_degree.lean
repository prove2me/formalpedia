-- Prove2me | solution 1 for mme_CW_2376_hash_budget_of_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T22:40:35.042291+00:00
-- url     : https://prove2.me/submissions/e2eaabc1-c8b3-4e75-b04e-90b5b33982b3

import Theorems.Thm_mme_CW_2376_hash_budget_select
import Theorems.Thm_mme_CW_2376_collision_universe_card_of_degree
import Theorems.Thm_mme_CW_2376_aggregate_budget_of_normalized_margin

open MME

set_option autoImplicit false

/-- Combine a uniform ambient star-degree bound with the normalized numerical
margin to obtain one vertex-closed hash state with the required target
surplus. -/
theorem solution
    (m p D Dstar : ℕ) (hm : 0 < m) [Fact p.Prime]
    (hp5 : 5 ≤ p) (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (V loss : ℝ) (hV : 0 ≤ V)
    (hT : ((cw2376AllExactTargetEdges m).card : ℝ) =
      V * (Dstar : ℝ))
    (hdeg : ∀ i : Fin 3, ∀ a ∈ cw2376AllExactTargetEdges m,
      ((cw2376MarginalSupportedUniverse m).filter
        (fun b => b.1 i = a.1 i)).card ≤ D)
    (hmargin :
      (p : ℝ) ^ 2 * loss + 3 * (Dstar : ℝ) * (D : ℝ) ≤
        (Dstar : ℝ) * (S.card : ℝ)) :
    ∃ E : Finset (CW2376MarginalSupportedAddress m),
      CW2376MarginalVertexClosed E ∧
        ((cw2376TargetAmbientCollisions E).card : ℝ) + V * loss ≤
          ((cw2376ExactTargetEdges E).card : ℝ) := by
  let N := cw2376ProfileLength m
  have hCnat : (cw2376AllTargetAmbientCollisions m).card ≤
      3 * (cw2376AllExactTargetEdges m).card * D :=
    mme_CW_2376_collision_universe_card_of_degree m D hdeg
  have hC :
      ((cw2376AllTargetAmbientCollisions m).card : ℝ) * (p : ℝ) ^ N ≤
        3 * ((cw2376AllExactTargetEdges m).card : ℝ) * (D : ℝ) *
          (p : ℝ) ^ N := by
    have hc' :
        ((cw2376AllTargetAmbientCollisions m).card : ℝ) ≤
          3 * ((cw2376AllExactTargetEdges m).card : ℝ) * (D : ℝ) := by
      exact_mod_cast hCnat
    exact mul_le_mul_of_nonneg_right hc' (by positivity)
  have haggregate :=
    mme_CW_2376_aggregate_budget_of_normalized_margin
      (N + 1) p (cw2376AllExactTargetEdges m).card S.card D Dstar
      V loss (by omega) hV hT hmargin
  have haggregate' :
      (p : ℝ) ^ (N + 2) * (V * loss) +
          3 * ((cw2376AllExactTargetEdges m).card : ℝ) * (D : ℝ) *
            (p : ℝ) ^ N ≤
        ((cw2376AllExactTargetEdges m).card : ℝ) * (S.card : ℝ) *
          (p : ℝ) ^ N := by
    simpa only [Nat.add_assoc, Nat.add_sub_cancel] using haggregate
  have hbudget :
      (p : ℝ) ^ (N + 2) * (V * loss) +
          ((cw2376AllTargetAmbientCollisions m).card : ℝ) *
            (p : ℝ) ^ N ≤
        ((cw2376AllExactTargetEdges m).card : ℝ) * (S.card : ℝ) *
          (p : ℝ) ^ N := by
    have hcadd := add_le_add_left hC
      ((p : ℝ) ^ (N + 2) * (V * loss))
    have hcadd' :
        (p : ℝ) ^ (N + 2) * (V * loss) +
            ((cw2376AllTargetAmbientCollisions m).card : ℝ) *
              (p : ℝ) ^ N ≤
          (p : ℝ) ^ (N + 2) * (V * loss) +
            3 * ((cw2376AllExactTargetEdges m).card : ℝ) * (D : ℝ) *
              (p : ℝ) ^ N := by
      simpa only [add_comm] using hcadd
    exact hcadd'.trans haggregate'
  obtain ⟨q, hclosed, hsurplus⟩ :=
    mme_CW_2376_hash_budget_select m p hm hp5 hpodd S hSrange hSfree
      (V * loss) (by simpa only [N] using hbudget)
  exact ⟨cw2376RetainedEdgesAtAugmentedState m p S q,
    hclosed, hsurplus⟩
