-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_nabs_zbi
-- name    : Formalism.FourierDecayAlt.P.Mx2.nabs_zbi
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:07:29.055934+00:00
-- url     : https://prove2.me/theorems/b64b905e-cbf4-48eb-8d86-cbbe3b75312c
-- title:
--   Mx2: nabs zbi
-- statement:
--   The Mx2 construction uses the nabs zbi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L343-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L343-L345

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

theorem Formalism.FourierDecayAlt.P.Mx2.nabs_zbi (a TT : ℝ) : nabsE a TT * (zbiP : Pr r) = zbiP * nabsE a TT + zbiP * zbiP := by sorry
