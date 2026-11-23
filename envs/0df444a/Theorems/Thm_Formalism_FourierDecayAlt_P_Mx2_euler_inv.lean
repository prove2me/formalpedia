-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_euler_inv
-- name    : Formalism.FourierDecayAlt.P.Mx2.euler_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:21.175927+00:00
-- url     : https://prove2.me/theorems/81a6479e-5187-469a-aa29-6d18a07a2a7b
-- title:
--   Mx2: euler inv
-- statement:
--   The Mx2 construction uses the euler inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L109-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L109-L115

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx2
variable {r : ℕ}

theorem Formalism.FourierDecayAlt.P.Mx2.euler_inv (v : Var r) (f : Fn r) (hf : f ≠ 0) : euler v f⁻¹ = -(f⁻¹ * f⁻¹ * euler v f) := by sorry
