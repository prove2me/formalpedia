-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_rep_qminor
-- name    : Formalism.FourierDecayAlt.P.OperatorRepresentations.rep_qminor
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:08:11.970463+00:00
-- url     : https://prove2.me/theorems/e843acdb-4689-434b-964d-b7f1ca5469fd
-- title:
--   Operator Representations: rep qminor
-- statement:
--   The Operator Representations construction uses the rep qminor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OperatorRepresentations.lean#L211-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OperatorRepresentations.lean#L211-L219

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

theorem Formalism.FourierDecayAlt.P.OperatorRepresentations.rep_qminor (hD : IsOpen D) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ) :
    Rep (qminor (EV k r i D E) a b u) (fun f => qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u f) := by sorry
