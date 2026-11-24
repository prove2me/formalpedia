-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_one_le_abs_of_int_ne_zero
-- name    : Formalism.HermitianLatticeCounting.P.one_le_abs_of_int_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:34.434169+00:00
-- url     : https://prove2.me/theorems/686ae4b5-fbd3-4f3e-83a8-0fefd05ee0cf
-- title:
--   P: one le abs of int ne zero
-- statement:
--   The P construction uses the one le abs of int ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/CircleIntegralInvSubEqZeroOfOutside.lean#L387-L393
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/CircleIntegralInvSubEqZeroOfOutside.lean#L387-L393

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

theorem Formalism.HermitianLatticeCounting.P.one_le_abs_of_int_ne_zero (y : ℝ) (z : ℤ) (h : y = (z : ℝ)) (hy : y ≠ 0) : 1 ≤ |y| := by sorry
