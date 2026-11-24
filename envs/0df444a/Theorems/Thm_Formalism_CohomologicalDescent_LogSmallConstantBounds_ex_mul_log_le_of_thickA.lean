-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_ex_mul_log_le_of_thickA
-- name    : Formalism.CohomologicalDescent.LogSmallConstantBounds.ex_mul_log_le_of_thickA
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:43:59.006493+00:00
-- url     : https://prove2.me/theorems/6f194aed-87d0-4f63-8c60-a650dd6ea238
-- title:
--   Log Small Constant Bounds: ex mul log le of thick A
-- statement:
--   The Log Small Constant Bounds construction uses the ex mul log le of thick A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L630-L640
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L630-L640

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

theorem Formalism.CohomologicalDescent.LogSmallConstantBounds.ex_mul_log_le_of_thickA {P : Par} (H : P.Hyp) (G : P.Large) {ι : Type} {D : SizeData₂ ι}
    (hA : D.ThickA P) {τ : ι} (hτ : τ ∈ D.T2) {l : ℕ} (hl : l.Prime) :
    (D.ex τ l : ℝ) * Real.log (l : ℝ) ≤ (P.Nr : ℝ) ^ 2 * P.L := by sorry
