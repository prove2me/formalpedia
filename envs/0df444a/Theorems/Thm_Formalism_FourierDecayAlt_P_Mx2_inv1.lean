-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_inv1
-- name    : Formalism.FourierDecayAlt.P.Mx2.inv1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:48.31761+00:00
-- url     : https://prove2.me/theorems/6e17b546-dd28-4fb0-afdb-aa901f68a789
-- title:
--   Mx2: inv1
-- statement:
--   The Mx2 construction uses the inv1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L463-L464
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L463-L464

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

theorem Formalism.FourierDecayAlt.P.Mx2.inv1 (f fb : Fn r) (h : f ≠ 0) (hb : fb ≠ 0) : fnP f fb * fnP f⁻¹ fb⁻¹ = 1 := by sorry
