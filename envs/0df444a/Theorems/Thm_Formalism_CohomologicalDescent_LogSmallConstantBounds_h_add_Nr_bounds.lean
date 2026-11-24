-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_h_add_Nr_bounds
-- name    : Formalism.CohomologicalDescent.LogSmallConstantBounds.h_add_Nr_bounds
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:44:35.388635+00:00
-- url     : https://prove2.me/theorems/f0d846f0-cc9f-4a33-bcb1-9b8f6756a0e5
-- title:
--   Log Small Constant Bounds: h add Nr bounds
-- statement:
--   The Log Small Constant Bounds construction uses the h add Nr bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L834-L849
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L834-L849

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical

theorem Formalism.CohomologicalDescent.LogSmallConstantBounds.h_add_Nr_bounds {P : Par} (H : P.Hyp) (G : P.Large) :
    P.h ≤ P.h + (P.Nr : ℝ) ∧ 1 < P.h + (P.Nr : ℝ) ∧ P.h + (P.Nr : ℝ) ≤ 3 * P.b ∧
      0 < Real.log (P.h + (P.Nr : ℝ)) ∧ Real.log (P.h + (P.Nr : ℝ)) ≤ P.L + 1.1 := by sorry
