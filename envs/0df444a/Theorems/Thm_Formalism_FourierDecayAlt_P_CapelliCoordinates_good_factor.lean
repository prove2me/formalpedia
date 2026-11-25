-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliCoordinates_good_factor
-- name    : Formalism.FourierDecayAlt.P.CapelliCoordinates.good_factor
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:25:03.379596+00:00
-- url     : https://prove2.me/theorems/e9cde2f5-a592-54ec-a02e-e4a703225a90
-- title:
--   Capelli Coordinates: good factor
-- statement:
--   The Capelli Coordinates construction uses the good factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliCoordinates.lean#L233-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliCoordinates.lean#L233-L239

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliCoordinates
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
open Formalism.FourierDecayAlt.P.CapelliCoordinates
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

theorem Formalism.FourierDecayAlt.P.CapelliCoordinates.good_factor {T : (Mx k r → E) → Mx k r → E} (hT : Qx2.Good k r i D T) (p : Prop) [Decidable p] (c : ℂ) :
    Qx2.Good k r i D (fun y : Mx k r → E => (if p then c • y else 0) + T y) := by sorry
