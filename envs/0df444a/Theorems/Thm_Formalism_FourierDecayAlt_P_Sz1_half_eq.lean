-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz1_half_eq
-- name    : Formalism.FourierDecayAlt.P.Sz1.half_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:48.366086+00:00
-- url     : https://prove2.me/theorems/fc204934-4bcd-495d-ab07-eb82a34532f8
-- title:
--   Sz1: half eq
-- statement:
--   The Sz1 construction uses the half eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MassRatioFormula.lean#L7-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MassRatioFormula.lean#L7-L11

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz1
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz1.half_eq (r : ℕ) : (2 * r + 2) * (2 * r + 2 - 1) / 2 = (r + 1) * (2 * r + 1) := by sorry
