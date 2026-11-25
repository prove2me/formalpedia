-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FrameEntries_frame_inv
-- name    : Formalism.FourierDecayAlt.P.FrameEntries.frame_inv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:03:46.124175+00:00
-- url     : https://prove2.me/theorems/37ec35d3-584a-55e8-9655-05ccd0ad53ea
-- title:
--   Frame Entries: frame inv
-- statement:
--   The Frame Entries construction uses the frame inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameEntries.lean#L162-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameEntries.lean#L162-L169

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
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.FrameEntries.frame_inv {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) {m : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
    {Bs : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : IsFrameOf k r [z] Bs) :
    IsFrameOf k r [g⁻¹ *ᵥ z] (fun a => g⁻¹ *ᵥ Bs a) := by sorry
