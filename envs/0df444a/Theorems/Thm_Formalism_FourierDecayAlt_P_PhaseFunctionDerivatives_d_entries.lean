-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_d_entries
-- name    : Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.d_entries
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:59.572218+00:00
-- url     : https://prove2.me/theorems/a4a8c475-ecd0-4378-b3a3-47ce9fb86789
-- title:
--   Phase Function Derivatives: d entries
-- statement:
--   The Phase Function Derivatives construction uses the d entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionDerivatives.lean#L595-L619
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionDerivatives.lean#L595-L619

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.d_entries {m : ℕ} (t σ ρ₁ : ℂ) (ρ' : Fin m → ℂ) (x : UT (m + 1) → ℂ) (B : Fin (m + 1) → ℂ) (T : ℝ)
    (hT : 0 ≤ T) (h : ∀ i j, ‖Mcoord t (strictUpper x) B (Fin.cons ρ₁ ρ') σ i j‖ ≤ T) :
    (∀ i j, ‖strictUpper x i j‖ ≤ T) ∧ (∀ i, ‖B i‖ ≤ T) ∧ ‖ρ₁‖ ≤ T ∧ (∀ k, ‖ρ' k‖ ≤ T) ∧ ‖σ‖ ≤ T := by sorry
