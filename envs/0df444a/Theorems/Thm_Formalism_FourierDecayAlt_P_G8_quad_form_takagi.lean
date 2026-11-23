-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G8_quad_form_takagi
-- name    : Formalism.FourierDecayAlt.P.G8.quad_form_takagi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:29.314981+00:00
-- url     : https://prove2.me/theorems/b02a7562-df74-47df-8715-ba56417a7b53
-- title:
--   G8: quad form takagi
-- statement:
--   The G8 construction uses the quad form takagi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnitaryInvariantGaussian.lean#L211-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnitaryInvariantGaussian.lean#L211-L213

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G8

theorem Formalism.FourierDecayAlt.P.G8.quad_form_takagi (d : ℕ) (W D : Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) :
    x ⬝ᵥ ((W * D * Wᵀ) *ᵥ x) = (Wᵀ *ᵥ x) ⬝ᵥ (D *ᵥ (Wᵀ *ᵥ x)) := by sorry
