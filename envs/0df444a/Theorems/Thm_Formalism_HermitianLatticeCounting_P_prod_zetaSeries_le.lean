-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_prod_zetaSeries_le
-- name    : Formalism.HermitianLatticeCounting.P.prod_zetaSeries_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:49.196246+00:00
-- url     : https://prove2.me/theorems/1e8f1982-315c-48c1-a24f-8218e7f79b39
-- title:
--   P: prod zeta Series le
-- statement:
--   The P construction uses the prod zeta Series le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LatticeSumBounds.lean#L1751-L1765
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LatticeSumBounds.lean#L1751-L1765

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

theorem Formalism.HermitianLatticeCounting.P.prod_zetaSeries_le (S : Finset ℕ) (hS : ∀ j ∈ S, 3 ≤ j) : ∏ j ∈ S, zetaR j ≤ Real.exp 0.356 := by sorry
