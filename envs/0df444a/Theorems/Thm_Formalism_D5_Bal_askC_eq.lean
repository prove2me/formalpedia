-- Prove2me | Theorems.Thm_Formalism_D5_Bal_askC_eq
-- name    : Formalism.D5.Bal.askC_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:03:24.259448+00:00
-- url     : https://prove2.me/theorems/1f06a05c-935b-44c1-b590-c21481bff685
-- title:
--   Bal: ask C eq
-- statement:
--   The Bal construction uses the ask C eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/Balance.lean#L178-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/Balance.lean#L178-L211

import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
open Formalism.D5.Bal
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem Formalism.D5.Bal.askC_eq (Hs : CycHost H) (ψ : AddChar (E0 × H) ℂ) (a w : ℝ) (ha : 0 < a) (hw : 0 < w) :
    ∑ n ∈ Icc 1 ⌊a / w⌋₊, (Λ n : ℂ) * Hs.cv ψ n * ((a / n - w : ℝ) : ℂ)
      = (w : ℂ) * GC Hs ψ (a / w) + (if ψ = 0 then
          ((a * Real.log a - a * Real.log w - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ)
          else -(a : ℂ) * Hs.ell ψ) := by sorry
