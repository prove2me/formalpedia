-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_farA_sum_succ
-- name    : Formalism.HermitianLatticeCounting.P.farA_sum_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:01.334865+00:00
-- url     : https://prove2.me/theorems/6e93751e-969f-4e12-8c96-3617d9ca145f
-- title:
--   P: far A sum succ
-- statement:
--   The P construction uses the far A sum succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/CoefficientLeOperatorNorm.lean#L1495-L1504
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/CoefficientLeOperatorNorm.lean#L1495-L1504

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P

theorem Formalism.HermitianLatticeCounting.P.farA_sum_succ {B h ε : ℝ} (hε : 0 < ε) (h32 : 32 * B ≤ h * ε) (h16 : 16 ≤ h * ε ^ 2) (m : ℕ) :
    ∑ k ∈ range m, farA B h ε (k+1) ≤ 2 * Real.exp (-(h * ε ^ 2 / 16)) := by sorry
