-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G7_affine_fibre
-- name    : Formalism.FourierDecayAlt.P.G7.affine_fibre
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:42:22.870871+00:00
-- url     : https://prove2.me/theorems/807784b7-8ff0-48c7-b75b-ffbebfa588b8
-- title:
--   G7: affine fibre
-- statement:
--   The G7 construction uses the affine fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralConvergesAbs.lean#L205-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralConvergesAbs.lean#L205-L233

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2

theorem Formalism.FourierDecayAlt.P.G7.affine_fibre {Y : Type} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν] (β : ℂ)
    (α γ : Y → ℂ) (hα : Measurable α) (hγ : Measurable γ) (h0 : ∀ᵐ y ∂ν, α y ≠ 0) :
    Measure.map (fun p : ℂ × Y => (α p.2 * p.1 + γ p.2, p.2))
      (((mu β).prod ν).withDensity (fun p => ((‖α p.2‖₊ ^ 2 : NNReal) : ENNReal))) = (mu β).prod ν := by sorry
