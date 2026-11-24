-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_Final_S4_global_assembly_doubled
-- name    : Formalism.HermitianLatticeCounting.Final.S4.global_assembly_doubled
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:09.469727+00:00
-- url     : https://prove2.me/theorems/d94da953-5b89-40b8-8f84-df70a953eb59
-- title:
--   S4: global assembly doubled
-- statement:
--   The S4 construction uses the global assembly doubled property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/GlobalAssemblyDoubled.lean#L7-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/GlobalAssemblyDoubled.lean#L7-L7

import Definitions.Def_Formalism_FlagUnipotentLattices_ConductorCharacterLeakBound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_GaussSumCharacterAverageBound
import Definitions.Def_Formalism_FlagUnipotentLattices_GlobalAssemblyDoubled
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.S4

theorem Formalism.HermitianLatticeCounting.Final.S4.global_assembly_doubled : Formalism.HermitianLatticeCounting.S4.NonGenericBoundLargeHeight := by sorry
