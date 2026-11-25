-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_actA_sum
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.actA_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:14:15.450917+00:00
-- url     : https://prove2.me/theorems/78290b9e-e418-4372-b832-592084a9e6fd
-- title:
--   Gauge: act A sum
-- statement:
--   The Gauge construction uses the act A sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGaugeCut.lean#L154-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGaugeCut.lean#L154-L159

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

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.actA_sum {ι : Type} (s : Finset ι) (x : ι → MA.A P (MA.DQ P)) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (∑ i ∈ s, x i) f = ∑ i ∈ s, MA.actA P (x i) f := by sorry
