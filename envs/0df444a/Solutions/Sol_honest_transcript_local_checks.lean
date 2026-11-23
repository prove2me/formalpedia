-- Prove2me | solution 1 for honest_transcript_local_checks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:45:09.63188+00:00
-- url     : https://prove2.me/submissions/beafe0f0-b77e-4485-9406-35d203ebaec4

import Definitions.Def_SimpleRbrFri_Soundness
import Definitions.Def_SimpleRbrFri_Completeness
import Theorems.Thm_honest_transcript_satisfies_local_check

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F)
    (challenges : FRIVerifierChallenges P)
    (T : FRITranscript P)
    (h_T : T = FRI_honest_transcript P f_0 challenges) :
    ∀ (j : Fin P.q_rep) (i : Fin P.num_foldings), FRI_local_check P f_0 T (T.s j) i :=
  fun j i ↦ honest_transcript_satisfies_local_check P f_0 challenges T h_T j i
