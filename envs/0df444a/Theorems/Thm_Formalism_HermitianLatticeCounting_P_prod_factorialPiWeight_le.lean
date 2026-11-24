-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_prod_factorialPiWeight_le
-- name    : Formalism.HermitianLatticeCounting.P.prod_factorialPiWeight_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:51.928829+00:00
-- url     : https://prove2.me/theorems/46016834-6e77-441e-8af6-d783f75bcbf0
-- title:
--   P: prod factorial Pi Weight le
-- statement:
--   The P construction uses the prod factorial Pi Weight le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LatticeSumBounds.lean#L1887-L1937
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LatticeSumBounds.lean#L1887-L1937

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

theorem Formalism.HermitianLatticeCounting.P.prod_factorialPiWeight_le (v : ℝ) (hv : 1 ≤ v) (k s : ℕ) (hs : 2 ≤ s) (hk : s + 2 ≤ k) :
    ∏ j ∈ Finset.Ioc 2 s, s5bA v j ≤
      (Real.pi ^ ((s - 2) * (k - s - 2)) * 17 *
        ((Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi)))) *
        ∏ j ∈ Finset.Ioc (k - s) k, s5bA v j := by sorry
