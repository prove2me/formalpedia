-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_revIn_lt
-- name    : Formalism.DoubleCosetMeasures.P.Supp.revIn_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:53:29.619531+00:00
-- url     : https://prove2.me/theorems/c39b9cdb-420f-4b84-96cc-4c56f7b49665
-- title:
--   Supp: rev In lt
-- statement:
--   The Supp construction uses the rev In lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L120-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L120-L127

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

theorem Formalism.DoubleCosetMeasures.P.Supp.revIn_lt : ∀ (s : List ℕ) (j : ℕ), j < s.sum → revIn s j < s.sum
  := by sorry
