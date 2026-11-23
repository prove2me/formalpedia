-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G5_mp_of_comp
-- name    : Formalism.FourierDecayAlt.P.G5.mp_of_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:42:12.233985+00:00
-- url     : https://prove2.me/theorems/acf25fe0-257f-43ad-9766-f9cbde33c8a8
-- title:
--   G5: mp of comp
-- statement:
--   The G5 construction uses the mp of comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L306-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L306-L310

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.G5.mp_of_comp {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {ν : Measure α} {μ : Measure β} {μ' : Measure γ} {J : α → β} {F : β → γ}
    (hJ : MeasurePreserving J ν μ) (hF : Measurable F) (h : MeasurePreserving (F ∘ J) ν μ') :
    MeasurePreserving F μ μ' := by sorry
