-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_ex_mul_log_le_of_thinA
-- name    : Formalism.CohomologicalDescent.LogSmallConstantBounds.ex_mul_log_le_of_thinA
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:45:19.901115+00:00
-- url     : https://prove2.me/theorems/09dbf770-fe7f-4536-a500-df94a100dcf9
-- title:
--   Log Small Constant Bounds: ex mul log le of thin A
-- statement:
--   The Log Small Constant Bounds construction uses the ex mul log le of thin A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L649-L671
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L649-L671

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

theorem Formalism.CohomologicalDescent.LogSmallConstantBounds.ex_mul_log_le_of_thinA {P : Par} (H : P.Hyp) (G : P.Large) {ι : Type} {D : SizeData₂ ι}
    (hA : D.ThinA P) (hW : D.Widths P) {τ : ι} (hτ : τ ∉ D.T2) {l : ℕ} (hl : l.Prime) :
    (D.ex τ l : ℝ) * Real.log (l : ℝ) ≤ (P.Nr : ℝ) ^ 2 * P.L := by sorry
