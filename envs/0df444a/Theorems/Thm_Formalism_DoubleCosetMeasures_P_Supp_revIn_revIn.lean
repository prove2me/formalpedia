-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_revIn_revIn
-- name    : Formalism.DoubleCosetMeasures.P.Supp.revIn_revIn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:34.21186+00:00
-- url     : https://prove2.me/theorems/6311b39d-06fb-453b-8f9d-0a2f863db89a
-- title:
--   Supp: rev In rev In
-- statement:
--   The Supp construction uses the rev In rev In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L129-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L129-L142

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_ExistsContinuousLowerUpperEntry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures.P.Supp

theorem Formalism.DoubleCosetMeasures.P.Supp.revIn_revIn : ∀ (s : List ℕ) (j : ℕ), j < s.sum → revIn s (revIn s j) = j
  := by sorry
