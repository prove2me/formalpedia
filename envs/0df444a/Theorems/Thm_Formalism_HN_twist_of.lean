-- Prove2me | Theorems.Thm_Formalism_HN_twist_of
-- name    : Formalism.HN.twist_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:27:34.201553+00:00
-- url     : https://prove2.me/theorems/e1470cab-9cb9-4bf6-bab1-b3e549e15392
-- title:
--   HN: twist of
-- statement:
--   The HN construction uses the twist of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/TwistFinrankEq.lean#L29-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/TwistFinrankEq.lean#L29-L99

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_TwistFinrankEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN

theorem Formalism.HN.twist_of (h1 : RescaleCovol) (h2 : PlLat) (h3 : ShiftInvariance.{0, 0, 0, 0}) : Twist := by sorry
