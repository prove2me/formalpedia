-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_toSm_add
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.toSm_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:37:13.767387+00:00
-- url     : https://prove2.me/theorems/c3c768f7-7b9f-4d08-8004-cf279a682f0c
-- title:
--   Gauge: to Sm add
-- statement:
--   The Gauge construction uses the to Sm add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGaugeCut.lean#L176-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGaugeCut.lean#L176-L179

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge
noncomputable section
variable (P : M.Par)

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.toSm_add {u v : MA.Qp P.r P.TT → ℂ} (hu : u ∈ MA.smSub P.r P.TT) (hv : v ∈ MA.smSub P.r P.TT) :
    MA.toSm P (u + v) = MA.toSm P u + MA.toSm P v := by sorry
