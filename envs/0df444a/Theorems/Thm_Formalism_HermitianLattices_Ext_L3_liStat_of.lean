-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_liStat_of
-- name    : Formalism.HermitianLattices.Ext.L3.liStat_of
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:36:58.217823+00:00
-- url     : https://prove2.me/theorems/9781d892-f9fb-567c-8cf4-adce8ee0a127
-- title:
--   L3: li Stat of
-- statement:
--   The L3 construction uses the li Stat of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LiStatOf.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LiStatOf.lean#L11-L22

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RepRatioEqZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LiPin
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatioHolds
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LiStatOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3

theorem Formalism.HermitianLattices.Ext.L3.liStat_of (hR : LIRatio) (hP : LIPin) : LIStat := by sorry
