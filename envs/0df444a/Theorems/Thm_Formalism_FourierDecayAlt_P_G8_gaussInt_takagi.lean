-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G8_gaussInt_takagi
-- name    : Formalism.FourierDecayAlt.P.G8.gaussInt_takagi
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:18.259142+00:00
-- url     : https://prove2.me/theorems/525d3614-6e05-477b-b63e-a4c80939ab3a
-- title:
--   G8: gauss Int takagi
-- statement:
--   The G8 construction uses the gauss Int takagi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnitaryInvariantGaussian.lean#L236-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnitaryInvariantGaussian.lean#L236-L251

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

theorem Formalism.FourierDecayAlt.P.G8.gaussInt_takagi (hU : UnitaryInvariant) (d : ℕ) (β t : ℂ) (W : Matrix (Fin d) (Fin d) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) (σ : Fin d → ℝ) (δ : ℝ) :
    gaussInt β d (W * Matrix.diagonal (fun i => ((σ i : ℝ) : ℂ)) * Wᵀ) t δ =
      ∏ k, ∫ w : ℂ, ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) * psi β (((σ k : ℂ) / t) * w ^ 2 / 2) ∂(mu β) := by sorry
