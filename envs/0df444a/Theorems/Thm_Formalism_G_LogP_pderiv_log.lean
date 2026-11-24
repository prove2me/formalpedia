-- Prove2me | Theorems.Thm_Formalism_G_LogP_pderiv_log
-- name    : Formalism.G.LogP.pderiv_log
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:23.769119+00:00
-- url     : https://prove2.me/theorems/5cee4d2e-69e1-4c06-864f-61ca4b50117d
-- title:
--   Log P: pderiv log
-- statement:
--   The Log P construction uses the pderiv log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean#L95-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean#L95-L101

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

theorem Formalism.G.LogP.pderiv_log {g : PowerSeries R} (hg : IsLog F g) :
    (PowerSeries.derivative R g).subst F.toPowerSeries * MvPowerSeries.pderiv R 1 F.toPowerSeries =
      atY (PowerSeries.derivative R g) := by sorry
