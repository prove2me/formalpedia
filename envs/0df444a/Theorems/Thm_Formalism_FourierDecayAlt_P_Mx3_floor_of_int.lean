-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_floor_of_int
-- name    : Formalism.FourierDecayAlt.P.Mx3.floor_of_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:11.904137+00:00
-- url     : https://prove2.me/theorems/29c2395a-7b36-473b-9e04-307be6103190
-- title:
--   Mx3: floor of int
-- statement:
--   The Mx3 construction uses the floor of int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InterlaceSignTwo.lean#L72-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InterlaceSignTwo.lean#L72-L75

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx3

theorem Formalism.FourierDecayAlt.P.Mx3.floor_of_int (x : ℝ) (h0 : 0 ≤ x) (z : ℤ) (hz : x = z) : ((⌊x⌋₊ : ℕ) : ℝ) = x := by sorry
