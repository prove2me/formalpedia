-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_lOneNorm_single
-- name    : Formalism.HermitianLatticeCounting.P.lOneNorm_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:09:28.682921+00:00
-- url     : https://prove2.me/theorems/686d432e-9925-4cdb-8caf-47748f94c0f4
-- title:
--   P: l One Norm single
-- statement:
--   The P construction uses the l One Norm single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L1075-L1076
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L1075-L1076

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
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms

theorem Formalism.HermitianLatticeCounting.P.lOneNorm_single {P : Type} (p : P) (c : ℂ) : lOneNorm (Finsupp.single p c) = ‖c‖ := by sorry
