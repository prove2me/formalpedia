-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBO_fsv_smul
-- name    : Formalism.FourierDecayAlt.P.PBO.fsv_smul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:08:21.345234+00:00
-- url     : https://prove2.me/theorems/cf41856b-5e24-5344-b345-a9624b01e73c
-- title:
--   PBO: fsv smul
-- statement:
--   The PBO construction uses the fsv smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormLeIntegralFsv.lean#L33-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormLeIntegralFsv.lean#L33-L40

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

theorem Formalism.FourierDecayAlt.P.PBO.fsv_smul (s u z : ℂ) : P5.fsv s u * z = 𝐞 (-⟪u, (π⁻¹ : ℝ) • isoQ s⟫) • z := by sorry
