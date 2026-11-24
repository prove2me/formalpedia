-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_sum_zetaSeries_sub_one_le
-- name    : Formalism.HermitianLatticeCounting.P.sum_zetaSeries_sub_one_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:29:55.719693+00:00
-- url     : https://prove2.me/theorems/8a0e7c6d-6f55-4a74-9cd5-2176fa8d318e
-- title:
--   P: sum zeta Series sub one le
-- statement:
--   The P construction uses the sum zeta Series sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LatticeSumBounds.lean#L1698-L1726
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LatticeSumBounds.lean#L1698-L1726

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

theorem Formalism.HermitianLatticeCounting.P.sum_zetaSeries_sub_one_le (N : ℕ) : ∑ j ∈ Finset.Icc 3 N, (zetaR j - 1) ≤ 0.356 := by sorry
