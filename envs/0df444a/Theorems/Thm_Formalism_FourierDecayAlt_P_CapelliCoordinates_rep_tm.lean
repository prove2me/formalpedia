-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliCoordinates_rep_tm
-- name    : Formalism.FourierDecayAlt.P.CapelliCoordinates.rep_tm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:10:41.43683+00:00
-- url     : https://prove2.me/theorems/106cbcbe-3479-4eea-98f9-047cbde3e63c
-- title:
--   Capelli Coordinates: rep tm
-- statement:
--   The Capelli Coordinates construction uses the rep tm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliCoordinates.lean#L447-L461
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliCoordinates.lean#L447-L461

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliCoordinates
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_id

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
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)}

theorem Formalism.FourierDecayAlt.P.CapelliCoordinates.rep_tm (hD : IsOpen D) {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (hB : ∀ a, inWb k r (Bs a))
    (P Q : Matrix (Fin (mdim k r (Fin.last r))) (Fin (mdim k r (Fin.last r))) ℂ)
    (ι : Fin m → Fin (mdim k r (Fin.last r))) (hι : Function.Injective ι)
    (hP : ∀ a c, P c (ι a) = Bs a (posL k r (Fin.last r) c))
    (hQ : ∀ b d, Q (ι b) d = herm (Hpk k r) (bvec (posL k r (Fin.last r) d)) (Bs b)) (u : ℂ) (a b : Fin m) :
    OperatorRepresentations.Rep (Tm (Econj (EV k r (Fin.last r) D E) P Q) u (ι a) (ι b))
      (fun y : Mx k r → E => (if id a = id b then u • y else 0) + RZ (Hpk k r) (unitB (Hpk k r) Bs (id a) (id b)) y) := by sorry
