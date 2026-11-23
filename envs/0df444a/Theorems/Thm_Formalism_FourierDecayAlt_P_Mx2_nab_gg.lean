-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_nab_gg
-- name    : Formalism.FourierDecayAlt.P.Mx2.nab_gg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:00.951368+00:00
-- url     : https://prove2.me/theorems/6bebbc5e-4d69-450b-9b0f-58227fccc3ec
-- title:
--   Mx2: nab gg
-- statement:
--   The Mx2 construction uses the nab gg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L178-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L178-L182

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

theorem Formalism.FourierDecayAlt.P.Mx2.nab_gg (a TT : ℝ) : nabE a TT * (ggP TT : Pr r) = ggP TT * nabE a TT + zbP := by sorry
