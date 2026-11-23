-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_disjointness_of_supports_holds
-- name    : Formalism.HermitianLatticeCounting.P.disjointness_of_supports_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:03:05.632811+00:00
-- url     : https://prove2.me/theorems/934dfcdd-2f53-4ed9-bb64-5b4e07e40d2f
-- title:
--   P: disjointness of supports holds
-- statement:
--   The P construction uses the disjointness of supports holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L51-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L51-L75

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
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms

theorem Formalism.HermitianLatticeCounting.P.disjointness_of_supports_holds : Formalism.HermitianLatticeCounting.ExpansionTerms.SeparatedPolydiscsDisjoint := by sorry
