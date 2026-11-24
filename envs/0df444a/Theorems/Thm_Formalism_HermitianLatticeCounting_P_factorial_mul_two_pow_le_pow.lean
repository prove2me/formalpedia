-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_factorial_mul_two_pow_le_pow
-- name    : Formalism.HermitianLatticeCounting.P.factorial_mul_two_pow_le_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:06.499847+00:00
-- url     : https://prove2.me/theorems/8e6fdb62-23de-41af-8f25-78bf2dcf1a3e
-- title:
--   P: factorial mul two pow le pow
-- statement:
--   The P construction uses the factorial mul two pow le pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IdealsOfNormEqIndexSet.lean#L461-L481
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IdealsOfNormEqIndexSet.lean#L461-L481

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IdealsOfNormEqIndexSet
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
open Formalism.SLP.P.CountO NumberField
open scoped nonZeroDivisors

theorem Formalism.HermitianLatticeCounting.P.factorial_mul_two_pow_le_pow (d : ℕ) (hd : 1 ≤ d) : (d.factorial : ℝ) * 2 ^ (d - 1) ≤ (d : ℝ) ^ d := by sorry
