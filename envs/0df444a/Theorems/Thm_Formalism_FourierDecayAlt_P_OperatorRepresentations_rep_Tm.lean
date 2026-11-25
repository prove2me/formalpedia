-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_rep_Tm
-- name    : Formalism.FourierDecayAlt.P.OperatorRepresentations.rep_Tm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:12:47.967902+00:00
-- url     : https://prove2.me/theorems/eed7da14-6095-4b99-a856-131254aa616d
-- title:
--   Operator Representations: rep Tm
-- statement:
--   The Operator Representations construction uses the rep Tm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OperatorRepresentations.lean#L202-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OperatorRepresentations.lean#L202-L209

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

theorem Formalism.FourierDecayAlt.P.OperatorRepresentations.rep_Tm (hD : IsOpen D) (u : ℂ) (a b : Fin (mdim k r i)) :
    Rep (Tm (EV k r i D E) u a b) (fun f => QuantumDeterminants.Top (EH k r) u (posL k r i a) (posL k r i b) f) := by sorry
