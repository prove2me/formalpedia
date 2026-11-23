-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_onSum_of
-- name    : Formalism.EigenvalueLevelCeiling.onSum_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:22.862042+00:00
-- url     : https://prove2.me/theorems/71a10d8c-80c9-47ac-a531-60e919e39ce9
-- title:
--   Eigenvalue Level Ceiling: on Sum of
-- statement:
--   The Eigenvalue Level Ceiling construction uses the on Sum of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/AbsorbLocalConditions.lean#L22-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/AbsorbLocalConditions.lean#L22-L65

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues

theorem Formalism.EigenvalueLevelCeiling.onSum_of (hP : PlaceSum) (hR : RamBasic) (hE : ErrSumGood) : OnSum := by sorry
