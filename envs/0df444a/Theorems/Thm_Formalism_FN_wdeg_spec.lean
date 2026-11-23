-- Prove2me | Theorems.Thm_Formalism_FN_wdeg_spec
-- name    : Formalism.FN.wdeg_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:25:06.887682+00:00
-- url     : https://prove2.me/theorems/521dfdc9-9c78-4391-b979-f0841c0b530b
-- title:
--   FN: wdeg spec
-- statement:
--   The FN construction uses the wdeg spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/NewtonSlope.lean#L11-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/NewtonSlope.lean#L11-L37

import Definitions.Def_Formalism_SuccessiveMinima_StatementNP
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NewtonSlope
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
variable {K : Type*} [NormedField K]

theorem Formalism.FN.wdeg_spec (a : ℕ → K) (r : ℝ) (hr : 0 < r) (h : ConvOn a r) (ha : a ≠ 0) :
    ‖a (wdeg a r)‖ * r ^ (wdeg a r) = gNorm a r ∧ 0 < gNorm a r := by sorry
