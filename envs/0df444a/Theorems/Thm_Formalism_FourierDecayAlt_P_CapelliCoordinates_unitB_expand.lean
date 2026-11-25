-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliCoordinates_unitB_expand
-- name    : Formalism.FourierDecayAlt.P.CapelliCoordinates.unitB_expand
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:26:30.322118+00:00
-- url     : https://prove2.me/theorems/ee2c6b3e-fc13-59a4-a7c9-552c87a0820d
-- title:
--   Capelli Coordinates: unit B expand
-- statement:
--   The Capelli Coordinates construction uses the unit B expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliCoordinates.lean#L383-L386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliCoordinates.lean#L383-L386

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
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.CapelliCoordinates.unitB_expand {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (hB : ∀ a, inWb k r (Bs a)) (a b : Fin m) :
    unitB (Hpk k r) Bs a b = ∑ c, ∑ d, (Bs a (posL k r (Fin.last r) c) *
      herm (Hpk k r) (bvec (posL k r (Fin.last r) d)) (Bs b)) •
        Matrix.single (posL k r (Fin.last r) c) (posL k r (Fin.last r) d) (1 : ℂ) := by sorry
