-- Prove2me | Theorems.Thm_FRI_W_large_propagation
-- name    : FRI_W_large_propagation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:32:43.005575+00:00
-- url     : https://prove2.me/theorems/be53588b-af6f-4202-acb3-5ae618d94204
-- title:
--   FRI W large propagation: FRI W large propagation
-- statement:
--   The FRI W large propagation construction uses the FRI W large propagation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L98-L124
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L98-L124

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
set_option autoImplicit true

theorem FRI_W_large_propagation {F : Type*} [Field F] [DecidableEq F] (P : FRIParameters F)
    (f_0 : P.D_0 → F) (T : FRITranscript P) (bound : ℝ)
    (h_domain_size : FRI_Domain_Size_Property P)
    (h_large_0 : (FRI_W P f_0 T 0).card ≥
      (1 - FRI_distance_star P f_0 bound) * (FRI_domain P 0).card) :
    ∀ i : Fin (P.num_foldings + 1), (FRI_W P f_0 T i).card ≥
      (1 - FRI_distance_star P f_0 bound) * (FRI_domain P i).card := by sorry
