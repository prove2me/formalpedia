-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_eq_sum_indicator
-- name    : Formalism.DoubleCosetMeasures.P.eq_sum_indicator
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:54.421312+00:00
-- url     : https://prove2.me/theorems/8e0507ae-0402-4d07-ba7f-5cfe4746744c
-- title:
--   P: eq sum indicator
-- statement:
--   The P construction uses the eq sum indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/DoubleCosetEqPreimage.lean#L32-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/DoubleCosetEqPreimage.lean#L32-L45

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_DoubleCosetEqPreimage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
variable {X : Type}
variable [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem Formalism.DoubleCosetMeasures.P.eq_sum_indicator (r : Setoid X) (f : X → E)
    (hf : ∀ x y, Quotient.mk r x = Quotient.mk r y → f x = f y)
    (t : Finset (Quotient r)) (ht : Function.support (fun q : Quotient r => f q.out) ⊆ t) :
    f = fun x => ∑ q ∈ t, (cls r q).indicator (fun _ => f q.out) x := by sorry
