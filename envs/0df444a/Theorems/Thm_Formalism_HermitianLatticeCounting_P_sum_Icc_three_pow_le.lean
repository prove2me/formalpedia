-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_sum_Icc_three_pow_le
-- name    : Formalism.HermitianLatticeCounting.P.sum_Icc_three_pow_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:33.613636+00:00
-- url     : https://prove2.me/theorems/16e17aca-f7a7-4fab-ba6f-2ee360536c2e
-- title:
--   P: sum Icc three pow le
-- statement:
--   The P construction uses the sum Icc three pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LatticeSumBounds.lean#L1635-L1654
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LatticeSumBounds.lean#L1635-L1654

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

theorem Formalism.HermitianLatticeCounting.P.sum_Icc_three_pow_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (N : ℕ) :
    ∑ j ∈ Finset.Icc 3 N, x ^ j ≤ x ^ 3 / (1 - x) := by sorry
