-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_bridge
-- name    : Formalism.FourierDecayAlt.P.OperatorRepresentations.Rep.bridge
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:10:31.356126+00:00
-- url     : https://prove2.me/theorems/e72a0b20-f364-48b3-85a6-186f9a6cfdb8
-- title:
--   Rep: bridge
-- statement:
--   The Rep construction uses the bridge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OperatorRepresentations.lean#L188-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OperatorRepresentations.lean#L188-L191

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

theorem Formalism.FourierDecayAlt.P.OperatorRepresentations.Rep.bridge (hD : IsOpen D) {X : Module.End ℂ (SV k r i D E)} {T L : (Mx k r → E) → Mx k r → E}
    (hX : Rep X T) (hL : ∀ f, ∀ g ∈ Glev k r i ∩ D, L f g = T f g) (f : Mx k r → E) (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (L f) ∧ ∀ g ∈ Glev k r i ∩ D, L f g = (X (Qr.mkV hD f hf)).1 g := by sorry
