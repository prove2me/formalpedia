-- Prove2me | Theorems.Thm_Formalism_FN_unit_eps
-- name    : Formalism.FN.unit_eps
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:25:08.483703+00:00
-- url     : https://prove2.me/theorems/94955418-5cc3-4d7b-bd97-1f1e9f527936
-- title:
--   FN: unit eps
-- statement:
--   The FN construction uses the unit eps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/NPUnit.lean#L7-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/NPUnit.lean#L7-L45

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

theorem Formalism.FN.unit_eps {K : Type*} [NormedField K] (b : ℕ → K) (r : ℝ) (hr : 0 < r) (hc : ConvOn b r)
    (hb : b ≠ 0) (hw : wdeg b r = 0) :
    ‖b 0‖ = gNorm b r ∧ 0 < gNorm b r ∧
    ∃ ε : ℝ, 0 ≤ ε ∧ ε < 1 ∧ ∀ k, 1 ≤ k → ‖b k‖ * r ^ k ≤ ε * gNorm b r := by sorry
