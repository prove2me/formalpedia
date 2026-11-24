-- Prove2me | Theorems.Thm_Formalism_FG_HeightVAux_main
-- name    : Formalism.FG.HeightVAux.main
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:40:43.147594+00:00
-- url     : https://prove2.me/theorems/5787c5e0-1f41-456e-8c6a-1368b7ea8faf
-- title:
--   Height VAux: main
-- statement:
--   The Height VAux construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/HeightV.lean#L156-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/HeightV.lean#L156-L332

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_HeightV
import Theorems.Thm_Formalism_FG_CoefficientBoundsFormalGroupWitt_main
import Theorems.Thm_Formalism_FG_FunctionalEquationHom_main
import Theorems.Thm_Formalism_FG_InjVAux_main
import Theorems.Thm_Formalism_FG_InvIntVAux_main
import Theorems.Thm_Formalism_FG_KeyVAux_main
import Theorems.Thm_Formalism_FG_ShiftFEAux_main
import Theorems.Thm_Formalism_LT_FrobP_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FG Formalism.FG.HeightVAux
open MvPowerSeries Formalism.G Formalism.LT
open PadicInt

theorem Formalism.FG.HeightVAux.main (hC : Formalism.FG.FunEqCongrV.{0, 0, 0}) : Formalism.FG.ShiftHeight := by sorry
