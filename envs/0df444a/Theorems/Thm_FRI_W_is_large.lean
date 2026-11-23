-- Prove2me | Theorems.Thm_FRI_W_is_large
-- name    : FRI_W_is_large
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:09:49.354604+00:00
-- url     : https://prove2.me/theorems/7cffdff6-a98a-45cb-a9ec-c8e1e9607b47
-- title:
--   FRI W is large: FRI W is large
-- statement:
--   The FRI W is large construction uses the FRI W is large property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L549-L557
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L549-L557

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_W_is_large
    (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P) (bound : ℝ)
    (h_W_large : ∀ i : Fin (P.num_foldings + 1),
        (FRI_W P f_0 T i).card ≥ (1 - FRI_distance_star P f_0 bound) * (FRI_domain P i).card)
    (i : Fin P.num_foldings) :
    FRI_Is_Large_Subset P f_0 bound i i.isLt (FRI_W P f_0 T i) := by sorry
