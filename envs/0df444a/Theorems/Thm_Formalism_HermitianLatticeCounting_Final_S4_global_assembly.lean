-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_Final_S4_global_assembly
-- name    : Formalism.HermitianLatticeCounting.Final.S4.global_assembly
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:31:03.354944+00:00
-- url     : https://prove2.me/theorems/2103ae4f-a7ee-4dd7-bcb8-10381ea00254
-- title:
--   S4: global assembly
-- statement:
--   The S4 construction uses the global assembly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/GlobalAssemblyDoubled.lean#L6-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/GlobalAssemblyDoubled.lean#L6-L6

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

theorem Formalism.HermitianLatticeCounting.Final.S4.global_assembly : Formalism.HermitianLatticeCounting.S4.WeightedAmplitudeSqSumBoundTwoTypeClasses := by sorry
