-- Prove2me | Theorems.Thm_Formalism_D5_sum_thick_term_eq_gaussSums
-- name    : Formalism.D5.sum_thick_term_eq_gaussSums
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:08:52.235799+00:00
-- url     : https://prove2.me/theorems/e9df9286-8689-44a1-8f3f-5bcbc811a174
-- title:
--   D5: sum thick term eq gauss Sums
-- statement:
--   The D5 construction uses the sum thick term eq gauss Sums property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/ThickAverage.lean#L285-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/ThickAverage.lean#L285-L304

import Definitions.Def_Formalism_ThickAverageLoss_ParametersAveragedDifferenceBound
import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
open Classical

theorem Formalism.D5.sum_thick_term_eq_gaussSums {m : ℕ} (Hs : CycHost H) (Nd : Nodes H m) (t : H) (j : Fin m) :
    ∑ u0 : H, thickZ Hs Nd u0 t j = ((Nd.T2.card : ℂ) / 2) * ((Nd.bj j : ℝ) : ℂ) *
      (GC Hs 0 (Nd.a t / Nd.bj j) + GC Hs Hs.psC (Nd.a t / Nd.bj j) - GC Hs Hs.chC (Nd.a t / Nd.bj j)
        - GC Hs Hs.chpsC (Nd.a t / Nd.bj j)) := by sorry
