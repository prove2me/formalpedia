-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_half_integer_neg_le_neg_half
-- name    : Formalism.HermitianLatticeCounting.P.half_integer_neg_le_neg_half
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:05.258129+00:00
-- url     : https://prove2.me/theorems/aa36af17-4b4e-47e2-b467-1905e3b8d57a
-- title:
--   P: half integer neg le neg half
-- statement:
--   The P construction uses the half integer neg le neg half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/CircleIntegralInvSubEqZeroOfOutside.lean#L376-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/CircleIntegralInvSubEqZeroOfOutside.lean#L376-L385

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalDS
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CircleIntegralInvSubEqZeroOfOutside
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset

theorem Formalism.HermitianLatticeCounting.P.half_integer_neg_le_neg_half (y : ℝ) (z : ℤ) (h : y = (z : ℝ) + 1 / 2) (hy : y < 0) : y ≤ -(1 / 2) := by sorry
