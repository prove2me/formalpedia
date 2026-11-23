-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G3_inner_int
-- name    : Formalism.FourierDecayAlt.P.G3.inner_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:29.508432+00:00
-- url     : https://prove2.me/theorems/6709505b-7b95-4d07-9711-9cb9666489cb
-- title:
--   G3: inner int
-- statement:
--   The G3 construction uses the inner int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AffineChangeOfVariables.lean#L60-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AffineChangeOfVariables.lean#L60-L65

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory
open scoped FourierTransform RealInnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G3

theorem Formalism.FourierDecayAlt.P.G3.inner_int (β ξ : ℂ) (f : ℂ → ℂ) :
    ∫ x : ℂ, f x * psi β (ξ * x) = 𝓕 f (al β * (starRingEnd ℂ) ξ) := by sorry
