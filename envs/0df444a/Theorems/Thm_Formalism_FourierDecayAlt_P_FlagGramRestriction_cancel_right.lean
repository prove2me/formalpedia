-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FlagGramRestriction_cancel_right
-- name    : Formalism.FourierDecayAlt.P.FlagGramRestriction.cancel_right
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:36:27.115164+00:00
-- url     : https://prove2.me/theorems/1fc4e5c9-9c62-496d-b4a4-76206edc91db
-- title:
--   Flag Gram Restriction: cancel right
-- statement:
--   The Flag Gram Restriction construction uses the cancel right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FlagGramRestriction.lean#L117-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FlagGramRestriction.lean#L117-L121

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentUpperFacts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagGramRestriction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FlagGramRestriction
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector UnipotentUpperFacts
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.FlagGramRestriction.cancel_right {m : Type*} [Fintype m] [DecidableEq m] (A X Y : Matrix m m ℂ) (hA : IsUnit A.det)
    (h : X * A = Y * A) : X = Y := by sorry
