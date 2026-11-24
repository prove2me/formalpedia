-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_op_sum_apply
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.op_sum_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:57:42.290201+00:00
-- url     : https://prove2.me/theorems/be744866-2cbe-4490-b468-1f95b74bc365
-- title:
--   Gauge: op sum apply
-- statement:
--   The Gauge construction uses the op sum apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGaugeCut.lean#L139-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGaugeCut.lean#L139-L141

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

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.op_sum_apply {ι : Type} (s : Finset ι) (X : ι → (MA.DQ P).Op) (g : (MA.DQ P).R) :
    (∑ i ∈ s, X i) g = ∑ i ∈ s, X i g := by sorry
