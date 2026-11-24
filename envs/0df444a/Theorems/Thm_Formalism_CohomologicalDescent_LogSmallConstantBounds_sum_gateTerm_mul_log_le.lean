-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_sum_gateTerm_mul_log_le
-- name    : Formalism.CohomologicalDescent.LogSmallConstantBounds.sum_gateTerm_mul_log_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:44:44.05763+00:00
-- url     : https://prove2.me/theorems/07afd500-dd1c-4ec5-81ca-b934b131f372
-- title:
--   Log Small Constant Bounds: sum gate Term mul log le
-- statement:
--   The Log Small Constant Bounds construction uses the sum gate Term mul log le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L908-L931
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L908-L931

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

theorem Formalism.CohomologicalDescent.LogSmallConstantBounds.sum_gateTerm_mul_log_le {P : Par} (H : P.Hyp) (G : P.Large) {ι : Type} {D : SizeData₂ ι}
    (hT : D.ShapeT P) {τ : ι} (hτ : τ ∈ D.T2) {R : Finset ℕ}
    (hR : ∀ l ∈ R, l.Prime ∧ P.lJ < (l : ℝ) ∧ (l : ℝ) ≤ P.h) :
    ∑ l ∈ R, gatedCoefficientTerm D P τ l * Real.log (l : ℝ) ≤
      (D.q τ : ℝ) * P.h * (1 + Real.log P.h) * Real.log P.h := by sorry
