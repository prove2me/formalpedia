-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G7_integral_affine_fibre
-- name    : Formalism.FourierDecayAlt.P.G7.integral_affine_fibre
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:00:04.478088+00:00
-- url     : https://prove2.me/theorems/b1bbaf7c-5d70-4e6f-b94c-587dd7b7a63e
-- title:
--   G7: integral affine fibre
-- statement:
--   The G7 construction uses the integral affine fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralConvergesAbs.lean#L235-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralConvergesAbs.lean#L235-L248

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

theorem Formalism.FourierDecayAlt.P.G7.integral_affine_fibre {Y : Type} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν] (β : ℂ)
    (α γ : Y → ℂ) (hα : Measurable α) (hγ : Measurable γ) (h0 : ∀ᵐ y ∂ν, α y ≠ 0)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (G : ℂ × Y → V)
    (hG : AEStronglyMeasurable G ((mu β).prod ν)) :
    ∫ p, G p ∂((mu β).prod ν) =
      ∫ p, ((‖α p.2‖ ^ 2 : ℝ) : ℂ) • G (α p.2 * p.1 + γ p.2, p.2) ∂((mu β).prod ν) := by sorry
