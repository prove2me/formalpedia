-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_partialDeriv_mul_fn
-- name    : Formalism.FourierDecayAlt.P.Mx2.partialDeriv_mul_fn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:22.433996+00:00
-- url     : https://prove2.me/theorems/c732a386-d98d-4898-802e-1cee9237b4af
-- title:
--   Mx2: partial Deriv mul fn
-- statement:
--   The Mx2 construction uses the partial Deriv mul fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L293-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L293-L294

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

theorem Formalism.FourierDecayAlt.P.Mx2.partialDeriv_mul_fn (l : Fin r) (f fb : Fn r) : pP l * fnP f fb = fnP f fb * pP l + fnP (euler (vc l) f) (euler (vcb l) fb) := by sorry
