-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_cutoff_comparison_nearby
-- name    : Formalism.HermitianLatticeCounting.P.cutoff_comparison_nearby
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:42.446065+00:00
-- url     : https://prove2.me/theorems/4723dd0f-b39c-4722-be77-d71e2d1825db
-- title:
--   P: cutoff comparison nearby
-- statement:
--   The P construction uses the cutoff comparison nearby property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L263-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L263-L290

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

theorem Formalism.HermitianLatticeCounting.P.cutoff_comparison_nearby (K ro abelian₂ : ℝ) (hK : 0 ≤ K) (hro : 0 < ro) (hLam : 0 < abelian₂) (D x : ℂ)
    (hx : ‖x - D‖ < ro / 2) :
    TruncationCutoff K abelian₂ ‖D‖ ≤ TruncationCutoff K (3 / 2 * max ro abelian₂) ‖x‖ := by sorry
