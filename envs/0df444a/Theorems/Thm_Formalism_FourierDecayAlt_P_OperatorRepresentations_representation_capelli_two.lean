-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_representation_capelli_two
-- name    : Formalism.FourierDecayAlt.P.OperatorRepresentations.representation_capelli_two
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:11:20.687852+00:00
-- url     : https://prove2.me/theorems/3f75ff0e-aff6-4d0a-9757-cdc7c0df34ab
-- title:
--   Operator Representations: representation capelli two
-- statement:
--   The Operator Representations construction uses the representation capelli two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OperatorRepresentations.lean#L244-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OperatorRepresentations.lean#L244-L261

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

theorem Formalism.FourierDecayAlt.P.OperatorRepresentations.representation_capelli_two (hD : IsOpen D) (z : Fin (2 * r + k + 1) → ℂ) (u : ℂ) (x ξ : Fin (mdim k r i) → ℂ) :
    Rep (ch2 (EV k r i D E) u (yV k r z i D E) x (etaV k r z i D E) ξ)
      (fun f => chat2L (EH k r) (posL k r i) u (yv k r z i) (fun _ => x) (ybv k r z i) (fun _ => ξ) f) := by sorry
