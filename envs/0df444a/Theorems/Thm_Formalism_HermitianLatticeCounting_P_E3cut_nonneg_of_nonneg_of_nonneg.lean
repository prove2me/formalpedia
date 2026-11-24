-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_E3cut_nonneg_of_nonneg_of_nonneg
-- name    : Formalism.HermitianLatticeCounting.P.E3cut_nonneg_of_nonneg_of_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:30:48.211924+00:00
-- url     : https://prove2.me/theorems/9ef753d6-8435-488a-981e-425303d35a35
-- title:
--   P: E3cut nonneg of nonneg of nonneg
-- statement:
--   The P construction uses the E3cut nonneg of nonneg of nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L251-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L251-L255

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

theorem Formalism.HermitianLatticeCounting.P.E3cut_nonneg_of_nonneg_of_nonneg (K L t : ℝ) (hL : 0 ≤ L) (ht : 0 ≤ t) : 0 ≤ TruncationCutoff K L t := by sorry
