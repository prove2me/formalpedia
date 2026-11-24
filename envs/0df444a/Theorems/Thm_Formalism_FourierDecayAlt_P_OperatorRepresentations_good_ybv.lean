-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_good_ybv
-- name    : Formalism.FourierDecayAlt.P.OperatorRepresentations.good_ybv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:08:31.679884+00:00
-- url     : https://prove2.me/theorems/91da647a-627c-4ad8-bebf-8c3a0042b5d2
-- title:
--   Operator Representations: good ybv
-- statement:
--   The Operator Representations construction uses the good ybv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OperatorRepresentations.lean#L86-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OperatorRepresentations.lean#L86-L87

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

theorem Formalism.FourierDecayAlt.P.OperatorRepresentations.good_ybv (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (mdim k r i)) :
    Qx2.Good k r i D (mulF (E := E) fun g => ybv k r z i g c) := by sorry
