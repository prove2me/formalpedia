-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_sum_residueIndicator_mul_log_le
-- name    : Formalism.CohomologicalDescent.LogSmallConstantBounds.sum_residueIndicator_mul_log_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:45:20.603702+00:00
-- url     : https://prove2.me/theorems/0673990c-9290-4a4f-b2e8-341b121cc131
-- title:
--   Log Small Constant Bounds: sum residue Indicator mul log le
-- statement:
--   The Log Small Constant Bounds construction uses the sum residue Indicator mul log le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L886-L898
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L886-L898

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

theorem Formalism.CohomologicalDescent.LogSmallConstantBounds.sum_residueIndicator_mul_log_le {P : Par} (H : P.Hyp) (G : P.Large) {ι : Type} {D : SizeData₂ ι}
    (hT : D.ShapeT P) {τ : ι} (hτ : τ ∈ D.T2) {R : Finset ℕ}
    (hR : ∀ l ∈ R, l.Prime ∧ P.lJ < (l : ℝ) ∧ (l : ℝ) ≤ P.h) :
    ∑ l ∈ R, IlInd l (D.xlo τ) (D.xhi τ) (D.maxB τ) * Real.log (l : ℝ) ≤
      (P.S + 1) * Real.log P.h := by sorry
