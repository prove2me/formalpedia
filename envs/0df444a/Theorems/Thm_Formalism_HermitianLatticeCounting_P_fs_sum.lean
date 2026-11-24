-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_fs_sum
-- name    : Formalism.HermitianLatticeCounting.P.fs_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:26.626143+00:00
-- url     : https://prove2.me/theorems/d90337bf-9c91-46ae-b502-997a7237931f
-- title:
--   P: fs sum
-- statement:
--   The P construction uses the fs sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/MinkowskiNumberDvdFactorial.lean#L310-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/MinkowskiNumberDvdFactorial.lean#L310-L321

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P

theorem Formalism.HermitianLatticeCounting.P.fs_sum (A x : ℝ) (hA0 : 0 ≤ A) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k r f : ℕ) (hk : r + 2 ≤ k) :
    0 ≤ ∑ j ∈ Finset.Icc 1 r, A * x ^ (j * (k - 1 - j) * f) ∧
    ∑ j ∈ Finset.Icc 1 r, A * x ^ (j * (k - 1 - j) * f) ≤ r * (A * x ^ ((k - 2) * f)) := by sorry
