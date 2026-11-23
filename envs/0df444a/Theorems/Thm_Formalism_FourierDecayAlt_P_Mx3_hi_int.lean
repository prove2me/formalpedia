-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_hi_int
-- name    : Formalism.FourierDecayAlt.P.Mx3.hi_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:34.465028+00:00
-- url     : https://prove2.me/theorems/8ef3fc01-cf5b-4fb6-8afb-95ba64ef2119
-- title:
--   Mx3: hi int
-- statement:
--   The Mx3 construction uses the hi int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InterlaceSignTwo.lean#L63-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InterlaceSignTwo.lean#L63-L70

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

theorem Formalism.FourierDecayAlt.P.Mx3.hi_int (P : Par) (hP : P.OK) (i : ℕ) (hi : i ∈ Icc 1 (P.k - 1)) : ∃ n : ℤ, P.hi i - P.u 1 + 1 / 2 = n := by sorry
