-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_geom_half_le
-- name    : Formalism.BranchingDeterminantCap.geom_half_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:20.579975+00:00
-- url     : https://prove2.me/theorems/c09fef26-4ebd-4b57-a54d-2949ac4ff540
-- title:
--   Branching Determinant Cap: geom half le
-- statement:
--   The Branching Determinant Cap construction uses the geom half le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Numeric.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Numeric.lean#L22-L23

import Definitions.Def_Formalism_BranchSandwichDivisors_NormLog
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Numeric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.BranchingDeterminantCap

theorem Formalism.BranchingDeterminantCap.geom_half_le (k : ℕ) : ∑ j ∈ range k, ((1 : ℝ) / 2) ^ j ≤ 2 := by sorry
