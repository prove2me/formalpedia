-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_integral_eq_finsum
-- name    : Formalism.DoubleCosetMeasures.P.integral_eq_finsum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:54:23.525487+00:00
-- url     : https://prove2.me/theorems/b211f357-f485-461a-aabe-3313c181932d
-- title:
--   P: integral eq finsum
-- statement:
--   The P construction uses the integral eq finsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/DoubleCosetEqPreimage.lean#L47-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/DoubleCosetEqPreimage.lean#L47-L80

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

theorem Formalism.DoubleCosetMeasures.P.integral_eq_finsum (r : Setoid X) (hr : ∀ q, IsOpen (cls r q)) (μ : Measure X)
    (f : X → E) (hf : ∀ x y, Quotient.mk r x = Quotient.mk r y → f x = f y)
    (hc : HasCompactSupport f)
    (hμ : (∀ q, μ (cls r q) < ⊤) ∨ (∀ q, μ (cls r q) = ⊤)) :
    ∫ x, f x ∂μ = ∑ᶠ q : Quotient r, (μ (cls r q)).toReal • f q.out := by sorry
