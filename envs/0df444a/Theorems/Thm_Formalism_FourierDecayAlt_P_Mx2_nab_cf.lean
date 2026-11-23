-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_nab_cf
-- name    : Formalism.FourierDecayAlt.P.Mx2.nab_cf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:07:17.874435+00:00
-- url     : https://prove2.me/theorems/bcd19a22-6866-47fd-b0d6-a81c872791c3
-- title:
--   Mx2: nab cf
-- statement:
--   The Mx2 construction uses the nab cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L346-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L346-L348

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

theorem Formalism.FourierDecayAlt.P.Mx2.nab_cf (a TT : ℝ) (f fb : Fn r) (h1 : euler vz f = 0) (h2 : euler vzb fb = 0) :
    nabE a TT * fnP f fb = fnP f fb * nabE a TT := by sorry
