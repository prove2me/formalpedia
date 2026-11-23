-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G8_diagF_eq_prod
-- name    : Formalism.FourierDecayAlt.P.G8.diagF_eq_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:20.809677+00:00
-- url     : https://prove2.me/theorems/6f05ea00-42c4-4770-a4e2-8b48b05058fe
-- title:
--   G8: diag F eq prod
-- statement:
--   The G8 construction uses the diag F eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnitaryInvariantGaussian.lean#L225-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnitaryInvariantGaussian.lean#L225-L234

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

theorem Formalism.FourierDecayAlt.P.G8.diagF_eq_prod (β : ℂ) (d : ℕ) (σ : Fin d → ℝ) (t : ℂ) (δ : ℝ) (y : Fin d → ℂ) :
    diagF β d σ t δ y =
      ∏ k, (((Real.exp (-δ * ‖y k‖ ^ 2) : ℝ) : ℂ) * psi β (((σ k : ℂ) / t) * (y k) ^ 2 / 2)) := by sorry
