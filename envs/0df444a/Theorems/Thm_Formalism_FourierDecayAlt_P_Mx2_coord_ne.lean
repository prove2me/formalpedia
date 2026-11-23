-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_coord_ne
-- name    : Formalism.FourierDecayAlt.P.Mx2.coord_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:29.945853+00:00
-- url     : https://prove2.me/theorems/32154cf8-dba4-4074-8624-47c65c1737a7
-- title:
--   Mx2: coord ne
-- statement:
--   The Mx2 construction uses the coord ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L55-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L55-L56

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

theorem Formalism.FourierDecayAlt.P.Mx2.coord_ne (r : ℕ) (v : Var r) : coord v ≠ 0 := by sorry
