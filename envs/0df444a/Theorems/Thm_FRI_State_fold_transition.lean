-- Prove2me | Theorems.Thm_FRI_State_fold_transition
-- name    : FRI_State_fold_transition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:16:35.298804+00:00
-- url     : https://prove2.me/theorems/c470c28a-1de5-4900-aa88-6c3e454b61bb
-- title:
--   FRI State fold transition: FRI State fold transition
-- statement:
--   Folding round transition: State at round i+1 equals State at round i OR bad event at round i
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Soundness.lean#L84-L89
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Soundness.lean#L84-L89

import Definitions.Def_SimpleRbrFri_QuerySoundness
import Definitions.Def_SimpleRbrFri_Soundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
  [MeasurableSpace F] [DiscreteMeasurableSpace F]
omit [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]

theorem FRI_State_fold_transition (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (T : FRITranscript P) (i : Fin P.num_foldings) :
    FRI_State P f_0 bound T (i + 1) ↔
    FRI_State P f_0 bound T i ∨
      FRI_BadEvent P f_0 bound i (FRI_oracle_at_round P f_0 T i i.isLt) (T.alpha i) := by sorry
