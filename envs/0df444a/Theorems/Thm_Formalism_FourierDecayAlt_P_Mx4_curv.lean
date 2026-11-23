-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_curv
-- name    : Formalism.FourierDecayAlt.P.Mx4.curv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:05:27.740278+00:00
-- url     : https://prove2.me/theorems/d2fde3dd-4f64-4c57-a33c-d777ae1cf60c
-- title:
--   Mx4: curv
-- statement:
--   The Mx4 construction uses the curv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L199-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L199-L234

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}

theorem Formalism.FourierDecayAlt.P.Mx4.curv (a TT : ℝ) :
    (-dzbP + (a : ℂ) • (zP * ggiP TT)) * (dzP + (a : ℂ) • (zbP * ggiP TT)) -
      (dzP + (a : ℂ) • (zbP * ggiP TT)) * (-dzbP + (a : ℂ) • (zP * ggiP TT)) =
      (algebraMap ℂ (Pr r) ((2 * a * TT : ℝ) : ℂ)) * ggiP TT * ggiP TT := by sorry
