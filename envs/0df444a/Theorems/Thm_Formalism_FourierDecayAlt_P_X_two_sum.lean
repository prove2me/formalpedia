-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_X_two_sum
-- name    : Formalism.FourierDecayAlt.P.X.two_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:08.565973+00:00
-- url     : https://prove2.me/theorems/d206042b-0a07-4273-8712-fe68bf42c141
-- title:
--   X: two sum
-- statement:
--   The X construction uses the two sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalingExponentIdentities.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalingExponentIdentities.lean#L23-L24

import Definitions.Def_Formalism_HermitianCurvature_StatementX
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalingExponentIdentities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix
open Formalism.FourierDecayAlt.P.X

theorem Formalism.FourierDecayAlt.P.X.two_sum (l : ℕ) : 2 * (∑ a ∈ Finset.range l, a) = l * (l - 1) := by sorry
