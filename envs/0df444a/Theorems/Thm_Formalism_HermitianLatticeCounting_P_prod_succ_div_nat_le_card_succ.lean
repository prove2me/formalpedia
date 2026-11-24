-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_prod_succ_div_nat_le_card_succ
-- name    : Formalism.HermitianLatticeCounting.P.prod_succ_div_nat_le_card_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:46.079619+00:00
-- url     : https://prove2.me/theorems/99497dae-1696-4f70-9cb0-88524ecc8e1a
-- title:
--   P: prod succ div nat le card succ
-- statement:
--   The P construction uses the prod succ div nat le card succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/CircleIntegralInvSubEqZeroOfOutside.lean#L55-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/CircleIntegralInvSubEqZeroOfOutside.lean#L55-L83

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

theorem Formalism.HermitianLatticeCounting.P.prod_succ_div_nat_le_card_succ (S : Finset ℕ) : (∀ y ∈ S, 1 ≤ y) →
    ∏ y ∈ S, (((y : ℝ) + 1) / (y : ℝ)) ≤ (S.card : ℝ) + 1 := by sorry
