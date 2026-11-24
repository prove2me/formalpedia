-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Qr_opV_apply
-- name    : Formalism.FourierDecayAlt.Qr.opV_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:55:30.555246+00:00
-- url     : https://prove2.me/theorems/322a15b7-7ce2-42d9-a52e-74cd0e43b4f9
-- title:
--   Qr: op V apply
-- statement:
--   The Qr construction uses the op V apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementQr.lean#L150-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementQr.lean#L150-L153

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_StatementQr
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {k r i D E}

theorem Formalism.FourierDecayAlt.Qr.opV_apply (hD : IsOpen D) {T : (Mx k r → E) → Mx k r → E} (hT : Qx2.Good k r i D T) (φ : SV k r i D E)
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) : (opV k r i D T φ).1 g = T φ.1 g := by sorry
