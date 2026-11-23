-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_partialDerivBar_def
-- name    : Formalism.FourierDecayAlt.P.Mx2.partialDerivBar_def
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:28:24.337331+00:00
-- url     : https://prove2.me/theorems/ff86bc92-b5f3-4367-8286-9cd7a5f67552
-- title:
--   Mx2: partial Deriv Bar def
-- statement:
--   The Mx2 construction uses the partial Deriv Bar def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L289-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L289-L291

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

theorem Formalism.FourierDecayAlt.P.Mx2.partialDerivBar_def (l : Fin r) : (pbP l : Pr r) = mk (mulOp 1 * euler (vcb l)) (-(mulOp 1 * euler (vc l))) := by sorry
