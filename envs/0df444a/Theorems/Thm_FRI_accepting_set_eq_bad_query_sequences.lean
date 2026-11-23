-- Prove2me | Theorems.Thm_FRI_accepting_set_eq_bad_query_sequences
-- name    : FRI_accepting_set_eq_bad_query_sequences
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:14:01.835809+00:00
-- url     : https://prove2.me/theorems/3487a626-1283-4189-9891-ac76e385bcf7
-- title:
--   FRI accepting set eq bad query sequences: FRI accepting set eq bad query sequences
-- statement:
--   The FRI accepting set eq bad query sequences construction uses the FRI accepting set eq bad query sequences property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L525-L540
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L525-L540

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_accepting_set_eq_bad_query_sequences (P : FRIParameters F) (f_0 : P.D_0 → F)
    (bound : ℝ) (T : FRITranscript P)
    (h_state : ¬ FRI_State P f_0 bound T P.num_foldings)
    (h_pass : FRI_final_oracle P f_0 T ∈ FRI_code P P.num_foldings) :
    {s : Fin P.q_rep → { x // x ∈ P.D_0 } |
      let T' := { T with s := s }
      FRI_State P f_0 bound T' (P.num_foldings + 1)} =
    {s : Fin P.q_rep → { x // x ∈ P.D_0 } | ∀ j : Fin P.q_rep, (s j).val ∈ FRI_W P f_0 T 0} := by sorry
