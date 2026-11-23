-- Prove2me | solution 1 for honest_transcript_no_bad_events
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:48:25.379729+00:00
-- url     : https://prove2.me/submissions/4f617f60-2117-45bd-8507-adcd2270139b

import Definitions.Def_SimpleRbrFri_Soundness
import Definitions.Def_SimpleRbrFri_Completeness
import Theorems.Thm_honest_transcript_all_in_code

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution
    (P : FRIParameters F)
    (f_0 : P.D_0 → F)
    (bound : ℝ)
    (h_f0_in_code : f_0 ∈ (FRI_code P 0).carrier)
    (challenges : FRIVerifierChallenges P)
    (T : FRITranscript P)
    (h_T : T = FRI_honest_transcript P f_0 challenges)
    (i : Fin P.num_foldings) :
    ¬ FRI_BadEvent P f_0 bound i (FRI_oracle_at_round P f_0 T i i.isLt) (T.alpha i) := by
  subst h_T
  intro ⟨S, _, ⟨_, _, _⟩, hu₃⟩
  refine hu₃ (FRI_oracle_at_round P f_0 (FRI_honest_transcript P f_0 challenges) i i.isLt) ?_ ?_
  · rcases i with ⟨_ | i, hi⟩
    · simp only [FRI_oracle_at_round, ↓reduceDIte]
      exact h_f0_in_code
    · simp only [FRI_oracle_at_round, Nat.add_one_ne_zero, ↓reduceDIte,
        FRI_honest_transcript, Fin.succ_mk, Subtype.coe_eta]
      exact honest_transcript_all_in_code P f_0 h_f0_in_code challenges ⟨i + 1, Nat.lt_succ_of_lt hi⟩
  · exact fun _ _ ↦ rfl
