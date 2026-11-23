-- Prove2me | solution 1 for honest_transcript_accepts_all_queries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:49:49.87028+00:00
-- url     : https://prove2.me/submissions/12cad0dd-c3e1-451f-ad42-83188d0862f8

import Definitions.Def_SimpleRbrFri_Soundness
import Definitions.Def_SimpleRbrFri_Completeness
import Theorems.Thm_FRI_Perfect_Completeness

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution
    (P : FRIParameters F)
    (f_0 : P.D_0 → F)
    (h_f0_in_code : f_0 ∈ (FRI_code P 0).carrier)
    (alpha : Fin P.num_foldings → F)
    (s : Fin P.q_rep → P.D_0) :
    let challenges := {alpha := alpha, s := s}
    let T := FRI_honest_transcript P f_0 challenges
    FRI_verifier_accepts P f_0 T :=
  FRI_Perfect_Completeness P f_0 h_f0_in_code _
