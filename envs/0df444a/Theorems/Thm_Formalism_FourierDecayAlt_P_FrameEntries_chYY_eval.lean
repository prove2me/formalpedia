-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FrameEntries_chYY_eval
-- name    : Formalism.FourierDecayAlt.P.FrameEntries.chYY_eval
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:44:23.876396+00:00
-- url     : https://prove2.me/theorems/a5857f01-a44c-41f1-b7cc-254191711633
-- title:
--   Frame Entries: ch YY eval
-- statement:
--   The Frame Entries construction uses the ch YY eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameEntries.lean#L192-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameEntries.lean#L192-L208

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
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
open Formalism.FourierDecayAlt.P.FrameEntries
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

theorem Formalism.FourierDecayAlt.P.FrameEntries.chYY_eval (hD : IsOpen D) (z : Fin (2 * r + k + 1) → ℂ) (u : ℂ) (ψ : SV k r i D E) {g : Mx k r}
    (hg : g ∈ Glev k r i ∩ D) :
    (chYY (EV k r i D E) u (yV k r z i D E) (etaV k r z i D E) ψ).1 g =
      (chatA (EV k r i D E) u (yv k r z i g) (ybv k r z i g) ψ).1 g := by sorry
