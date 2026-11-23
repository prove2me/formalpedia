-- Prove2me | solution 1 for honest_transcript_all_in_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:46:39.192807+00:00
-- url     : https://prove2.me/submissions/5dd113d7-8551-4ced-96c5-fcd1d03e1fc3

import Definitions.Def_SimpleRbrFri_Soundness
import Definitions.Def_SimpleRbrFri_Completeness
import Theorems.Thm_honest_fold_preserves_code

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F)
    (h_f0_in_code : f_0 ∈ (FRI_code P 0).carrier)
    (challenges : FRIVerifierChallenges P) :
    ∀ i : Fin (P.num_foldings + 1),
    FRI_honest_messages P f_0 challenges.alpha i ∈ FRI_code P i := by
  intro i
  induction i using Fin.induction with
  | zero =>
    -- Base case: f_0 ∈ FRI_code P 0
    unfold FRI_honest_messages
    exact h_f0_in_code
  | succ i ih =>
    -- Inductive: honest_fold_preserves_code shows folding preserves membership
    have h_fold := honest_fold_preserves_code P ⟨i.val, i.isLt⟩
      (FRI_honest_messages P f_0 challenges.alpha i.castSucc) ih (challenges.alpha ⟨i.val, i.isLt⟩)
    have h_eq : FRI_honest_messages P f_0 challenges.alpha i.succ =
        FRI_honest_fold P ⟨i.val, i.isLt⟩
          (FRI_honest_messages P f_0 challenges.alpha i.castSucc) (challenges.alpha ⟨i.val, i.isLt⟩) := by
      funext x
      simp only [FRI_honest_messages, Fin.succ, Fin.castSucc, i.isLt, ↓reduceDIte]
      rfl
    exact h_eq ▸ h_fold
