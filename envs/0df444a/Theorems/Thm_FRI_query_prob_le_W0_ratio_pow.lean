-- Prove2me | Theorems.Thm_FRI_query_prob_le_W0_ratio_pow
-- name    : FRI_query_prob_le_W0_ratio_pow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:15:06.077723+00:00
-- url     : https://prove2.me/theorems/9dbbce4b-8dd4-4c50-8588-dae180c14c7d
-- title:
--   FRI query prob le W0 ratio pow: FRI query prob le W0 ratio pow
-- statement:
--   The FRI query prob le W0 ratio pow construction uses the FRI query prob le W0 ratio pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L651-L679
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L651-L679

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_query_prob_le_W0_ratio_pow [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ) (T : FRITranscript P)
    (h_state : ¬ FRI_State P f_0 bound T P.num_foldings)
    (h_pass : FRI_final_oracle P f_0 T ∈ FRI_code P P.num_foldings)
    (h_nonempty : Nonempty { x // x ∈ P.D_0 }) :
    FRI_query_prob P f_0 bound T ≤
    ENNReal.ofReal ((((FRI_W P f_0 T 0).card : ℝ) / (P.D_0.card : ℝ)) ^ P.q_rep) := by sorry
