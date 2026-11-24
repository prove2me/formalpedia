-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_summable_one_div_add_one_pow
-- name    : Formalism.HermitianLatticeCounting.P.summable_one_div_add_one_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:34.121155+00:00
-- url     : https://prove2.me/theorems/179cef6a-4d53-42a0-acac-80284fda7820
-- title:
--   P: summable one div add one pow
-- statement:
--   The P construction uses the summable one div add one pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LatticeSumBounds.lean#L1611-L1614
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LatticeSumBounds.lean#L1611-L1614

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P

theorem Formalism.HermitianLatticeCounting.P.summable_one_div_add_one_pow (j : ℕ) (hj : 2 ≤ j) : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ j) := by sorry
