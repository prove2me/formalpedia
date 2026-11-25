-- Prove2me | Theorems.Thm_Formalism_FN_unit_norm
-- name    : Formalism.FN.unit_norm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:24:39.278437+00:00
-- url     : https://prove2.me/theorems/d803150e-d7f5-5d72-a087-86de5252d77a
-- title:
--   FN: unit norm
-- statement:
--   The FN construction uses the unit norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/NPUnit.lean#L47-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/NPUnit.lean#L47-L66

import Definitions.Def_Formalism_SuccessiveMinima_DefsNP
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NewtonSlope
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NPUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FN
open Filter Topology

theorem Formalism.FN.unit_norm {K : Type} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (b : ℕ → K) (r : ℝ) (hr : 0 < r) (hc : ConvOn b r) (hb : b ≠ 0) (hw : wdeg b r = 0)
    (x : K) (hx : ‖x‖ ≤ r) : ‖evalS b x‖ = gNorm b r := by sorry
