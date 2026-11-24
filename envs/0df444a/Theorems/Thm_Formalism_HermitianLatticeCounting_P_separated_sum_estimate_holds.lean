-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_separated_sum_estimate_holds
-- name    : Formalism.HermitianLatticeCounting.P.separated_sum_estimate_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:22.468243+00:00
-- url     : https://prove2.me/theorems/834bc894-0b34-43e1-a175-b39b5e69bf1c
-- title:
--   P: separated sum estimate holds
-- statement:
--   The P construction uses the separated sum estimate holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L1155-L1155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L1155-L1155

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms

theorem Formalism.HermitianLatticeCounting.P.separated_sum_estimate_holds : Formalism.HermitianLatticeCounting.ExpansionTerms.SeparatedCutoffSum := by sorry
