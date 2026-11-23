-- Prove2me | solution 1 for honest_transcript_satisfies_local_check
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:42:37.078971+00:00
-- url     : https://prove2.me/submissions/2d1f8253-ad96-4b0f-a2d4-a5e7821f6d17

import Definitions.Def_SimpleRbrFri_Soundness
import Definitions.Def_SimpleRbrFri_Completeness
import Theorems.Thm_honest_fold_satisfies_fold_check
import Theorems.Thm_FRI_domain_zero_eq_D0
import Theorems.Thm_folded_query_in_domain


set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F)
    (challenges : FRIVerifierChallenges P)
    (T : FRITranscript P)
    (h_T : T = FRI_honest_transcript P f_0 challenges)
    (j : Fin P.q_rep) (i : Fin P.num_foldings) :
    FRI_local_check P f_0 T (T.s j) i := by
  subst h_T
  let z := folded_query P (challenges.s j).val (i : ℕ).succ
  have hz_in_domain : z ∈ FRI_domain P (↑i + 1) :=
    folded_query_in_domain P _ (challenges.s j).property _ (Nat.succ_le_of_lt i.isLt)
  unfold FRI_local_check FRI_honest_transcript
  -- Show LHS = RHS via intermediate form using honest_fold_satisfies_fold_check
  have h_lhs : Fold (FRI_domain P ↑i) (P.m i)
      (fun x ↦ FRI_get_val P f_0 (FRI_honest_transcript P f_0 challenges) i.castSucc x)
      ((FRI_honest_transcript P f_0 challenges).alpha i) z =
      Fold (FRI_domain P ↑i) (P.m i)
        (extend_by_zero (FRI_domain P ↑i) (FRI_honest_messages P f_0 challenges.alpha i.castSucc))
        (challenges.alpha i) z := by
    congr 2
    · ext x
      simp only [FRI_honest_transcript, FRI_get_val, extend_by_zero, Fin.coe_castSucc]
      split_ifs with h0 hx_D0 hx_dom hx_dom'
      · -- i = 0, x ∈ D_0, x ∈ FRI_domain P i: unfold FRI_honest_messages at 0
        obtain ⟨i_val, i_lt⟩ := i
        simp only at h0
        subst h0
        unfold FRI_honest_messages
        simp only [Fin.castSucc]
        rfl
      · -- i = 0, x ∈ D_0, x ∉ FRI_domain P i: contradiction via FRI_domain P 0 = D_0
        simp only [h0, FRI_domain_zero_eq_D0 P] at hx_dom
        exact absurd hx_D0 hx_dom
      · -- i = 0, x ∉ D_0, x ∈ FRI_domain P i: contradiction
        simp only [h0, FRI_domain_zero_eq_D0 P] at hx_dom'
        exact absurd hx_dom' hx_D0
      · rfl  -- i = 0, x ∉ D_0, x ∉ FRI_domain P i
      · -- i ≠ 0, x ∈ FRI_domain P i: prove indices equal
        have h_sub_add : ↑i - 1 + 1 = (↑i : ℕ) := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h0)
        congr 1
        · ext; simp only [Fin.val_succ, Fin.coe_castSucc]; omega
        · exact (Subtype.heq_iff_coe_eq (fun y ↦ by simp only [h_sub_add])).mpr rfl
      · rfl  -- i ≠ 0, x ∉ FRI_domain P i

  have h_rhs : FRI_get_val P f_0 (FRI_honest_transcript P f_0 challenges) i.succ z =
      extend_by_zero (FRI_domain P (↑i + 1))
        (FRI_honest_fold P i (FRI_honest_messages P f_0 challenges.alpha i.castSucc)
          (challenges.alpha i)) z := by
    simp only [FRI_honest_transcript, FRI_get_val, extend_by_zero, Fin.val_succ]
    split_ifs with h0 hx_D0 hx_dom <;> first | grind | skip
    -- Main case: z ∈ FRI_domain P (↑i + 1)
    unfold FRI_honest_messages
    simp only [Fin.succ, Nat.add_sub_cancel]
    split_ifs with hi
    · -- i.val < num_foldings: handle dependent type mismatches
      have h_idx_nat := Nat.add_sub_cancel (↑i) 1
      convert rfl using 5
      all_goals first | rfl | exact Fin.ext h_idx_nat | ext
      conv_rhs => unfold FRI_honest_messages
      have h_eq : i.castSucc = (⟨↑i, by omega⟩ : Fin (P.num_foldings + 1)) :=
        Fin.ext (by simp [Fin.coe_castSucc])
      cases h_eq
      rfl
    · exact absurd i.isLt hi
  have h_fold := honest_fold_satisfies_fold_check P i
    (FRI_honest_messages P f_0 challenges.alpha i.castSucc)
    (challenges.alpha i) z hz_in_domain

  calc Fold (FRI_domain P ↑i) (P.m i)
         (fun x ↦ FRI_get_val P f_0 (FRI_honest_transcript P f_0 challenges) i.castSucc x)
         ((FRI_honest_transcript P f_0 challenges).alpha i) z
      = Fold (FRI_domain P ↑i) (P.m i)
          (extend_by_zero (FRI_domain P ↑i) (FRI_honest_messages P f_0 challenges.alpha i.castSucc))
          (challenges.alpha i) z := h_lhs
    _ = extend_by_zero (FRI_domain P (↑i + 1))
          (FRI_honest_fold P i (FRI_honest_messages P f_0 challenges.alpha i.castSucc)
            (challenges.alpha i)) z := h_fold
    _ = FRI_get_val P f_0 (FRI_honest_transcript P f_0 challenges) i.succ z := h_rhs.symm
