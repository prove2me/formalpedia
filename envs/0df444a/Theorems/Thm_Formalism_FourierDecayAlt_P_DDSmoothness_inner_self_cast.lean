-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_inner_self_cast
-- name    : Formalism.FourierDecayAlt.P.DDSmoothness.inner_self_cast
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:27:22.313719+00:00
-- url     : https://prove2.me/theorems/01c202bf-1027-4cb2-b159-b3cab0f3f3fe
-- title:
--   DDSmoothness: inner self cast
-- statement:
--   The DDSmoothness construction uses the inner self cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/L2NormScaling.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/L2NormScaling.lean#L18-L23

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L2NormScaling
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate
noncomputable section
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DDSmoothness
open Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

theorem Formalism.FourierDecayAlt.P.DDSmoothness.inner_self_cast (a : Wp) : ⟪a, a⟫_ℂ = ((‖a‖ ^ 2 : ℝ) : ℂ) := by sorry
