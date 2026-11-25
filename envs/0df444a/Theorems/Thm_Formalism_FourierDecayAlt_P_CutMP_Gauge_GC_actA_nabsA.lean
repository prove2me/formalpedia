-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_actA_nabsA
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.actA_nabsA
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:23:58.487058+00:00
-- url     : https://prove2.me/theorems/aa266ed8-d5b5-45c7-ada0-ea7d408cfc84
-- title:
--   GC: act A nabs A
-- statement:
--   The GC construction uses the act A nabs A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTConnGaugeA.lean#L165-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTConnGaugeA.lean#L165-L170

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GTConnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTConnGaugeA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.actA_nabsA (P : M.Par) (g : M.Ty P → MA.SmQ P.r P.TT) (ρ : M.Ty P) :
    MA.actA P (MA.nabsA P (MA.DQ P)) g ρ =
      -dzbQ P (g ρ) + (M.aC P ρ : ℂ) • mulQ P (MA.DQ P).zP (mulQ P ((MA.DQ P).ggiP P.TT) (g ρ)) := by sorry
