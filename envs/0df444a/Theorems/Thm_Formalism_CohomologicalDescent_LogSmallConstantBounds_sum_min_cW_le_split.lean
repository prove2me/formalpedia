-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_sum_min_cW_le_split
-- name    : Formalism.CohomologicalDescent.LogSmallConstantBounds.sum_min_cW_le_split
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:45:06.81216+00:00
-- url     : https://prove2.me/theorems/00ace33b-f2bb-4f67-b60f-a801607cf22f
-- title:
--   Log Small Constant Bounds: sum min c W le split
-- statement:
--   The Log Small Constant Bounds construction uses the sum min c W le split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L787-L832
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L787-L832

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

theorem Formalism.CohomologicalDescent.LogSmallConstantBounds.sum_min_cW_le_split {P : Par} (H : P.Hyp) (G : P.Large) {ι : Type} {D : SizeData₂ ι}
    (hA : D.ThickA P) (hC : D.CloudA P) (hNW : D.NoWindow P) {τ : ι} (hτ : τ ∈ D.T2)
    {Q : Finset ℕ} (hQ : ∀ l ∈ Q, l.Prime ∧ P.lJ < (l : ℝ) ∧ ¬ P.Excl l) :
    ∑ l ∈ Q, min (D.ex τ l : ℝ) (D.cW P τ l) * Real.log (l : ℝ) ≤
      ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * (P.h + (P.Nr : ℝ)) *
          ∑ l ∈ Q.filter (fun l : ℕ => (l : ℝ) ≤ P.h), Real.log (l : ℝ) / ((l : ℝ) - 1)
      + 6 * ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) *
          ∑ l ∈ Q.filter (fun l : ℕ => (l : ℝ) ≤ P.h), Real.log (l : ℝ)
      + (P.k : ℝ) * P.S * ∑ l ∈ Q.filter (fun l : ℕ => (l : ℝ) ≤ P.h), Real.log (l : ℝ) / (l : ℝ)
      + (P.k : ℝ) * ∑ l ∈ Q.filter (fun l : ℕ => (l : ℝ) ≤ P.h),
          IlInd l (D.xlo τ) (D.xhi τ) (D.maxB τ) * Real.log (l : ℝ)
      + ∑ l ∈ Q.filter (fun l : ℕ => (l : ℝ) ≤ P.h), gatedCoefficientTerm D P τ l * Real.log (l : ℝ)
      + (D.q τ : ℝ) * P.h * ∑ l ∈ Q.filter (fun l : ℕ => (l : ℝ) ≤ P.h),
          (1 + max 0 (Real.log (P.h / (l : ℝ)))) * (Real.log (l : ℝ) / (l : ℝ)) := by sorry
