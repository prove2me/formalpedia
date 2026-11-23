-- Prove2me | Theorems.Thm_FRI_card_bad_query_sequences
-- name    : FRI_card_bad_query_sequences
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:15:23.957582+00:00
-- url     : https://prove2.me/theorems/87f6c73d-9150-4f6d-ad6b-afe317d8da9f
-- title:
--   FRI card bad query sequences: FRI card bad query sequences
-- statement:
--   Cardinality of bad query sequences.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L431-L447
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L431-L447

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_card_bad_query_sequences (P : FRIParameters F) (f_0 : P.D_0 → F)
    (T : FRITranscript P) :
    (Finset.univ.filter (fun s : Fin P.q_rep → { x // x ∈ P.D_0 } ↦
      ∀ j : Fin P.q_rep, (s j).val ∈ FRI_W P f_0 T 0)).card =
    (FRI_W P f_0 T 0).card ^ P.q_rep := by sorry
