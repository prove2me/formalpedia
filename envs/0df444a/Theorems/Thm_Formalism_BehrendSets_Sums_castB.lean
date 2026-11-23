-- Prove2me | Theorems.Thm_Formalism_BehrendSets_Sums_castB
-- name    : Formalism.BehrendSets.Sums.castB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:11:53.433904+00:00
-- url     : https://prove2.me/theorems/eb4c3730-e438-4ab2-a5d6-a14835f6aaf4
-- title:
--   Sums: cast B
-- statement:
--   The Sums construction uses the cast B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/TwoLeCastOfTwoLe.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/TwoLeCastOfTwoLe.lean#L23-L28

import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_TwoLeCastOfTwoLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Real
noncomputable section
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Sums

theorem Formalism.BehrendSets.Sums.castB (M k : ℕ) (hM : 2 ≤ M) :
    (((M * (k + 1) - 1 : ℕ)) : ℝ) = (M : ℝ) * ((k : ℝ) + 1) - 1 := by sorry
