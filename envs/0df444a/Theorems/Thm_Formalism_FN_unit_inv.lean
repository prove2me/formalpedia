-- Prove2me | Theorems.Thm_Formalism_FN_unit_inv
-- name    : Formalism.FN.unit_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:36.061036+00:00
-- url     : https://prove2.me/theorems/631ca402-ac9c-4833-9637-2e2cfa9e1035
-- title:
--   FN: unit inv
-- statement:
--   The FN construction uses the unit inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/NPUnit.lean#L68-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/NPUnit.lean#L68-L174

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

theorem Formalism.FN.unit_inv {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K]
    (b : ℕ → K) (r : ℝ) (hr : 0 < r) (hc : ConvOn b r) (hb : b ≠ 0) (hw : wdeg b r = 0) :
    ∃ u : ℕ → K, ConvOn u r ∧ cmul b u = fun n => if n = 0 then 1 else 0 := by sorry
