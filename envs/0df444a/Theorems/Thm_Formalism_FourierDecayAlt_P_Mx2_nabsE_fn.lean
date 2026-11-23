-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_nabsE_fn
-- name    : Formalism.FourierDecayAlt.P.Mx2.nabsE_fn
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:44.087963+00:00
-- url     : https://prove2.me/theorems/2d75ec09-eecb-4f60-8db1-5dbd1022f43d
-- title:
--   Mx2: nabs E fn
-- statement:
--   The Mx2 construction uses the nabs E fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L154-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L154-L158

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

theorem Formalism.FourierDecayAlt.P.Mx2.nabsE_fn (a TT : ℝ) (f fb : Fn r) :
    nabsE a TT * fnP f fb = fnP f fb * nabsE a TT - fnP ((coord vzb)⁻¹ * euler vzb f) ((coord vz)⁻¹ * euler vz fb) := by sorry
