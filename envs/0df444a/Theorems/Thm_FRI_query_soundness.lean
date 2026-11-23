-- Prove2me | Theorems.Thm_FRI_query_soundness
-- name    : FRI_query_soundness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:15:41.878787+00:00
-- url     : https://prove2.me/theorems/d1a835c5-109d-4ec0-9d2d-f393387836e6
-- title:
--   FRI query soundness: FRI query soundness
-- statement:
--   The FRI query soundness construction uses the FRI query soundness property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L684-L705
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L684-L705

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_query_soundness [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ) (T : FRITranscript P)
    (h_state : ¬ FRI_State P f_0 bound T P.num_foldings)
    (h_domain_size : FRI_Domain_Size_Property P)
    (h_D_pos : ∀ i : Fin (P.num_foldings + 1), (FRI_domain P i).card > 0) :
    FRI_query_prob P f_0 bound T ≤
      ENNReal.ofReal ((1 - FRI_distance_star P f_0 bound) ^ P.q_rep) := by sorry
