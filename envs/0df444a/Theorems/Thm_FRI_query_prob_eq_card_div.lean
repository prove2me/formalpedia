-- Prove2me | Theorems.Thm_FRI_query_prob_eq_card_div
-- name    : FRI_query_prob_eq_card_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:13:44.704056+00:00
-- url     : https://prove2.me/theorems/af75aaf4-e6ca-46a5-ae5c-c27076e7ebb5
-- title:
--   FRI query prob eq card div: FRI query prob eq card div
-- statement:
--   The FRI query prob eq card div construction uses the FRI query prob eq card div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L453-L470
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L453-L470

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
open scoped Classical

theorem FRI_query_prob_eq_card_div [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ) (T : FRITranscript P)
    (h_nonempty : Nonempty { x // x ∈ P.D_0 }) :
    FRI_query_prob P f_0 bound T =
    (Finset.univ.filter (fun s ↦
      let T' := { T with s := s }
      FRI_State P f_0 bound T' (P.num_foldings + 1))).card /
        (Fintype.card (Fin P.q_rep → { x // x ∈ P.D_0 }) : ENNReal) := by sorry
