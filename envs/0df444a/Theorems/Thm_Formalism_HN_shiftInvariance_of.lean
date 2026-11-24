-- Prove2me | Theorems.Thm_Formalism_HN_shiftInvariance_of
-- name    : Formalism.HN.shiftInvariance_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:27:14.748489+00:00
-- url     : https://prove2.me/theorems/aa1bef02-b5bb-4d80-8692-db05d0d8ff1d
-- title:
--   HN: shift Invariance of
-- statement:
--   The HN construction uses the shift Invariance of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/ShiftInvariance.lean#L138-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/ShiftInvariance.lean#L138-L184

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
universe u v w w₂

theorem Formalism.HN.shiftInvariance_of (h1 : MuChar.{u, v, w}) (h1' : MuChar.{u, v, w₂})
    (h4 : HNSlopes.{u, v, w}) : ShiftInvariance.{u, v, w, w₂} := by sorry
