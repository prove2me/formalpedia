-- Prove2me | Theorems.Thm_Formalism_G_LogP_evalYZero_atY
-- name    : Formalism.G.LogP.evalYZero_atY
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:28.476799+00:00
-- url     : https://prove2.me/theorems/fa5d056b-a803-4d1d-8f76-65d47d7de865
-- title:
--   Log P: eval YZero at Y
-- statement:
--   The Log P construction uses the eval YZero at Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean#L88-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean#L88-L93

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open Formalism Formalism.G Formalism.G.LogP
open Formalism.G.LogCR
variable {R : Type*} [CommRing R]
variable (F : FormalGroup R)

theorem Formalism.G.LogP.evalYZero_atY (φ : PowerSeries R) :
    MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), 0] (atY φ) =
      PowerSeries.C (PowerSeries.constantCoeff φ) := by sorry
