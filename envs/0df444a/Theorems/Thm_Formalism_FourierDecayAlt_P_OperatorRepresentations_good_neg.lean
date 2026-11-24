-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_good_neg
-- name    : Formalism.FourierDecayAlt.P.OperatorRepresentations.good_neg
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:08:12.278995+00:00
-- url     : https://prove2.me/theorems/64247a57-2052-4da9-a008-4acd142658d4
-- title:
--   Operator Representations: good neg
-- statement:
--   The Operator Representations construction uses the good neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OperatorRepresentations.lean#L89-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OperatorRepresentations.lean#L89-L91

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.OperatorRepresentations
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

theorem Formalism.FourierDecayAlt.P.OperatorRepresentations.good_neg {T : (Mx k r → E) → Mx k r → E} (hT : Qx2.Good k r i D T) :
    Qx2.Good k r i D (fun f x => -T f x) := by sorry
