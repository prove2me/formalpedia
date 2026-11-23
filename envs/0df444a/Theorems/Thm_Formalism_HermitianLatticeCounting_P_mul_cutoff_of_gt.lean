-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_mul_cutoff_of_gt
-- name    : Formalism.HermitianLatticeCounting.P.mul_cutoff_of_gt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:09:43.644205+00:00
-- url     : https://prove2.me/theorems/dc403b9d-3c73-4873-b9db-b69160717fb6
-- title:
--   P: mul cutoff of gt
-- statement:
--   The P construction uses the mul cutoff of gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L125-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L125-L132

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

theorem Formalism.HermitianLatticeCounting.P.mul_cutoff_of_gt {K L y : ℝ} (hK : 0 ≤ K) (hL : 0 < L) (h : L < y) :
    y * TruncationCutoff K L y = L ^ K * y ^ (1 - K) := by sorry
