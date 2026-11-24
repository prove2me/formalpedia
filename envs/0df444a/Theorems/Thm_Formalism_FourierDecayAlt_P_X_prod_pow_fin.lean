-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_X_prod_pow_fin
-- name    : Formalism.FourierDecayAlt.P.X.prod_pow_fin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:06.21496+00:00
-- url     : https://prove2.me/theorems/02a433e6-b473-4962-a17f-5a57141420ff
-- title:
--   X: prod pow fin
-- statement:
--   The X construction uses the prod pow fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalingExponentIdentities.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalingExponentIdentities.lean#L19-L21

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

theorem Formalism.FourierDecayAlt.P.X.prod_pow_fin {K : Type} [Field K] (κ : K) (l : ℕ) :
    (∏ a : Fin l, κ ^ (a : ℕ)) = κ ^ (∑ a ∈ Finset.range l, a) := by sorry
