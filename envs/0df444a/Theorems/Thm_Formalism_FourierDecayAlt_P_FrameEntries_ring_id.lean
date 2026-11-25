-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FrameEntries_ring_id
-- name    : Formalism.FourierDecayAlt.P.FrameEntries.ring_id
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:38:34.06582+00:00
-- url     : https://prove2.me/theorems/692c0728-c2c3-5884-b70b-3dfbebd10ab3
-- title:
--   Frame Entries: ring id
-- statement:
--   The Frame Entries construction uses the ring id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameEntries.lean#L227-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameEntries.lean#L227-L237

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

theorem Formalism.FourierDecayAlt.P.FrameEntries.ring_id (hA : AlgDet) (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) :
    tV k r z z' i D E (Y + 1) 0 0 * tV k r z z' i D E Y 1 1 - tV k r z z' i D E (Y + 1) 1 0 * tV k r z z' i D E Y 0 1 =
      -(chYY (EV k r i D E) (uC k r i Y) (yV k r z i D E) (etaV k r z i D E) *
        chatA (EV k r i D E) (uC k r i Y) (xv k r z' i) (xbv k r z' i)) := by sorry
