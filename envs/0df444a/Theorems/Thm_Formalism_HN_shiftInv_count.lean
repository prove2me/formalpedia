-- Prove2me | Theorems.Thm_Formalism_HN_shiftInv_count
-- name    : Formalism.HN.shiftInv_count
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:29.734308+00:00
-- url     : https://prove2.me/theorems/470669ca-d3d4-41bb-b8de-ad59e8b4dccb
-- title:
--   HN: shift Inv count
-- statement:
--   The HN construction uses the shift Inv count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/ShiftInvariance.lean#L81-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/ShiftInvariance.lean#L81-L94

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

theorem Formalism.HN.shiftInv_count (c : ℝ) (k m : ℕ) :
    (∑ i ∈ Finset.range m, if i < k then c else 0) = c * ((min k m : ℕ) : ℝ) := by sorry
