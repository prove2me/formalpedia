-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBO_norm_le_integral_fsv
-- name    : Formalism.FourierDecayAlt.P.PBO.norm_le_integral_fsv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:27:35.32903+00:00
-- url     : https://prove2.me/theorems/809d7c3a-593d-43aa-a2dd-611fd8b4b3b4
-- title:
--   PBO: norm le integral fsv
-- statement:
--   The PBO construction uses the norm le integral fsv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormLeIntegralFsv.lean#L42-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormLeIntegralFsv.lean#L42-L98

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormLeIntegralFsv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBO

theorem Formalism.FourierDecayAlt.P.PBO.norm_le_integral_fsv (φ : ℂ → ℂ) (hφ : Continuous φ) (hi : MeasureTheory.Integrable φ)
    (hΞ : MeasureTheory.Integrable (fun s : ℂ => ∫ t : ℂ, P5.fsv s t * φ t)) (t : ℂ) :
    ‖φ t‖ ≤ ∫ s : ℂ, ‖∫ u : ℂ, P5.fsv s u * φ u‖ := by sorry
