-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_nabE_fn
-- name    : Formalism.FourierDecayAlt.P.Mx2.nabE_fn
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:33.762405+00:00
-- url     : https://prove2.me/theorems/cd111133-7e7d-4a42-8a1e-69379e8e4f75
-- title:
--   Mx2: nab E fn
-- statement:
--   The Mx2 construction uses the nab E fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L148-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L148-L152

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

theorem Formalism.FourierDecayAlt.P.Mx2.nabE_fn (a TT : ℝ) (f fb : Fn r) :
    nabE a TT * fnP f fb = fnP f fb * nabE a TT + fnP ((coord vz)⁻¹ * euler vz f) ((coord vzb)⁻¹ * euler vzb fb) := by sorry
