-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_nabs_zb
-- name    : Formalism.FourierDecayAlt.P.Mx2.nabs_zb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:26:46.440778+00:00
-- url     : https://prove2.me/theorems/3b19d7bc-10ae-438b-b588-41e234cd06c1
-- title:
--   Mx2: nabs zb
-- statement:
--   The Mx2 construction uses the nabs zb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L189-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L189-L191

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

theorem Formalism.FourierDecayAlt.P.Mx2.nabs_zb (a TT : ℝ) : nabsE a TT * (zbP : Pr r) = zbP * nabsE a TT - 1 := by sorry
