-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_cyc_val
-- name    : Formalism.HermitianLatticeCounting.P.cyc_val
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:40:34.278802+00:00
-- url     : https://prove2.me/theorems/2048c684-c9be-5a47-907c-9e32111518b0
-- title:
--   P: cyc val
-- statement:
--   The P construction uses the cyc val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/InterlacingOfBlocksSecondCase.lean#L124-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/InterlacingOfBlocksSecondCase.lean#L124-L131

import Definitions.Def_Formalism_FlagUnipotentLattices_MemLpTwoOfOneTop
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_InterlacingOfBlocksSecondCase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S8 MeasureTheory Filter Topology TensorProduct Finset
set_option linter.all false
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P

theorem Formalism.HermitianLatticeCounting.P.cyc_val {m : ℕ} (i j : Fin (m + 1)) :
    ((Fin.cycleRange i j : Fin (m + 1)) : ℕ) =
      if (j : ℕ) < i then (j : ℕ) + 1 else if (j : ℕ) = i then 0 else (j : ℕ) := by sorry
