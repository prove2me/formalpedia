-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_pbP_0
-- name    : Formalism.FourierDecayAlt.P.Mx2.pbP_0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:55.015047+00:00
-- url     : https://prove2.me/theorems/bbd277c2-fbae-4166-94c9-2d7908f7986a
-- title:
--   Mx2: pb P 0
-- statement:
--   The Mx2 construction uses the pb P 0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L399-L400
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L399-L400

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

theorem Formalism.FourierDecayAlt.P.Mx2.pbP_0 (l : Fin r) (f fb : Fn r) (h1 : euler (vcb l) f = 0) (h2 : euler (vc l) fb = 0) :
    pbP l * fnP f fb = fnP f fb * pbP l := by sorry
