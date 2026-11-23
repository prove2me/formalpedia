-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_inv2
-- name    : Formalism.FourierDecayAlt.P.Mx2.inv2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:44.571696+00:00
-- url     : https://prove2.me/theorems/81d82939-428a-4104-a7d6-f6a808461677
-- title:
--   Mx2: inv2
-- statement:
--   The Mx2 construction uses the inv2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L465-L466
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L465-L466

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

theorem Formalism.FourierDecayAlt.P.Mx2.inv2 (f fb : Fn r) (h : f ≠ 0) (hb : fb ≠ 0) : fnP f⁻¹ fb⁻¹ * fnP f fb = 1 := by sorry
