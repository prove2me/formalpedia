-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_sum_J_mul_log_le_totalBound
-- name    : Formalism.CohomologicalDescent.LogSmallConstantBounds.sum_J_mul_log_le_totalBound
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:44:43.656542+00:00
-- url     : https://prove2.me/theorems/b028ef47-56a1-4e3f-b29b-bd588be483cd
-- title:
--   Log Small Constant Bounds: sum J mul log le total Bound
-- statement:
--   The Log Small Constant Bounds construction uses the sum J mul log le total Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L966-L1095
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L966-L1095

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

theorem Formalism.CohomologicalDescent.LogSmallConstantBounds.sum_J_mul_log_le_totalBound (rs3 : PrimeCountingBound) {P : Par} (H : P.Hyp) (G : P.Large) {ι : Type} [Fintype ι]
    {D : SizeData₂ ι} (I : D.Inputs P) (XC XD : ℝ)
    (hXC : ∀ τ ∈ D.T2, ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime ∧ (l : ℝ) ≤ P.lJ) →
      ∑ l ∈ Q, (D.ex τ l : ℝ) * Real.log (l : ℝ) ≤ XC)
    (hXD : ∀ τ ∈ D.T2, ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime ∧ P.lJ < (l : ℝ) ∧ ¬ P.Excl l) →
      ∑ l ∈ Q, min (D.ex τ l : ℝ) (D.cW P τ l) * Real.log (l : ℝ) ≤
        XD + 2 * (P.k : ℝ) * (P.S + 1) * (P.L + 2))
    (Q : Finset ℕ) (hQ : ∀ l ∈ Q, l.Prime) :
    ∑ l ∈ Q, (D.J l : ℝ) * Real.log (l : ℝ) ≤ totalBound P D.T2.card (XC + XD) := by sorry
