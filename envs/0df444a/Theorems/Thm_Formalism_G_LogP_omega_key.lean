-- Prove2me | Theorems.Thm_Formalism_G_LogP_omega_key
-- name    : Formalism.G.LogP.omega_key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:24.738342+00:00
-- url     : https://prove2.me/theorems/3ea278aa-20fd-4e80-8fb5-b540943ba2e4
-- title:
--   Log P: omega key
-- statement:
--   The Log P construction uses the omega key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean#L167-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean#L167-L207

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

theorem Formalism.G.LogP.omega_key :
    (omegaF F).subst F.toPowerSeries =
      MvPowerSeries.pderiv R 1 F.toPowerSeries * atY (omegaF F) := by sorry
