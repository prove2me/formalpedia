-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_ydat_facts
-- name    : Formalism.HermitianLatticeCounting.P.ydat_facts
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:46:50.622738+00:00
-- url     : https://prove2.me/theorems/dc9a05c9-34ff-4392-ac6f-52231d993102
-- title:
--   P: ydat facts
-- statement:
--   The P construction uses the ydat facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/CoefficientLeOperatorNorm.lean#L545-L563
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/CoefficientLeOperatorNorm.lean#L545-L563

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

theorem Formalism.HermitianLatticeCounting.P.ydat_facts {n f : ℕ} {rd g b : ℝ} (hn : 1 ≤ n) (hf : 1 ≤ f) (hrd : 1 ≤ rd) (hg : 1 ≤ g)
    (hb : 2 ≤ b) : 2 ≤ Ydat n f rd g b ∧ (n:ℝ) ≤ Ydat n f rd g b ∧ (f:ℝ) ≤ Ydat n f rd g b ∧
      rd ≤ Ydat n f rd g b ∧ g ≤ Ydat n f rd g b ∧ b ≤ Ydat n f rd g b := by sorry
