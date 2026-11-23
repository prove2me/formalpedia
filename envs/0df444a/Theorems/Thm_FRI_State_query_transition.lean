-- Prove2me | Theorems.Thm_FRI_State_query_transition
-- name    : FRI_State_query_transition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:16:48.226066+00:00
-- url     : https://prove2.me/theorems/acc2d3ba-aeee-40f7-a245-88801e10dc4d
-- title:
--   FRI State query transition: FRI State query transition
-- statement:
--   Query round transition: State at round k+1 equals State at round k OR verifier accepts
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Soundness.lean#L93-L97
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Soundness.lean#L93-L97

import Definitions.Def_SimpleRbrFri_QuerySoundness
import Definitions.Def_SimpleRbrFri_Soundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
  [MeasurableSpace F] [DiscreteMeasurableSpace F]
omit [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]

theorem FRI_State_query_transition (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (T : FRITranscript P) :
    FRI_State P f_0 bound T (P.num_foldings + 1) ↔
    FRI_State P f_0 bound T P.num_foldings ∨ FRI_verifier_accepts P f_0 T := by sorry
