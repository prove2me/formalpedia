-- Prove2me | Theorems.Thm_FRI_in_D0_of_in_W0_classical
-- name    : FRI_in_D0_of_in_W0_classical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:08:55.208892+00:00
-- url     : https://prove2.me/theorems/9867ae24-cd13-47b4-8a1e-afe4cdfb6bdc
-- title:
--   FRI in D0 of in W0 classical: FRI in D0 of in W0 classical
-- statement:
--   The FRI in D0 of in W0 classical construction uses the FRI in D0 of in W0 classical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L450-L452
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L450-L452

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_in_D0_of_in_W0_classical (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P)
    (x : F) (hx : x ∈ FRI_W P f_0 T 0) : x ∈ P.D_0 := by sorry
