-- Prove2me | Theorems.Thm_Formalism_HN_twist_finrank_eq
-- name    : Formalism.HN.twist_finrank_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:38:24.886721+00:00
-- url     : https://prove2.me/theorems/8b4f10d8-c6bd-40bb-8591-f4d3bf9875df
-- title:
--   HN: twist finrank eq
-- statement:
--   The HN construction uses the twist finrank eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/TwistFinrankEq.lean#L12-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/TwistFinrankEq.lean#L12-L27

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

theorem Formalism.HN.twist_finrank_eq (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] :
    (Module.finrank ℚ K : ℝ) = 2 * (nPl K : ℝ) := by sorry
