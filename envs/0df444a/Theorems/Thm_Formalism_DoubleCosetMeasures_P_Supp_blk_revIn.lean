-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_blk_revIn
-- name    : Formalism.DoubleCosetMeasures.P.Supp.blk_revIn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:45:44.916286+00:00
-- url     : https://prove2.me/theorems/ed8e445c-2da2-4fbd-ac83-0981e3f02dd4
-- title:
--   Supp: blk rev In
-- statement:
--   The Supp construction uses the blk rev In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L144-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L144-L157

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

theorem Formalism.DoubleCosetMeasures.P.Supp.blk_revIn : ∀ (s : List ℕ) (j : ℕ), j < s.sum → blk s (revIn s j) = blk s j
  := by sorry
