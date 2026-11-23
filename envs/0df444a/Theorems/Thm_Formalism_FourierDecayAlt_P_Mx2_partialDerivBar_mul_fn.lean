-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_partialDerivBar_mul_fn
-- name    : Formalism.FourierDecayAlt.P.Mx2.partialDerivBar_mul_fn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:49.955801+00:00
-- url     : https://prove2.me/theorems/d6f97d1f-0e25-4097-a7c3-1ebcf02bb156
-- title:
--   Mx2: partial Deriv Bar mul fn
-- statement:
--   The Mx2 construction uses the partial Deriv Bar mul fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L295-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L295-L296

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

theorem Formalism.FourierDecayAlt.P.Mx2.partialDerivBar_mul_fn (l : Fin r) (f fb : Fn r) : pbP l * fnP f fb = fnP f fb * pbP l + fnP (euler (vcb l) f) (euler (vc l) fb) := by sorry
