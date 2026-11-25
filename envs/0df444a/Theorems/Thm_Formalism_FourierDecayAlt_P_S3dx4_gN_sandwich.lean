-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_gN_sandwich
-- name    : Formalism.FourierDecayAlt.P.S3dx4.gN_sandwich
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:32:32.690827+00:00
-- url     : https://prove2.me/theorems/add96ca5-db90-55e6-9576-0b68b02ed7db
-- title:
--   S3dx4: g N sandwich
-- statement:
--   The S3dx4 construction uses the g N sandwich property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GNSandwich.lean#L39-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GNSandwich.lean#L39-L78

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OoConvOf
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GNSandwich
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.S3dx4.gN_sandwich (hNI : NormInv) {x A y : Mx k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hA : A ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hy : y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) {b : ℝ}
    (hb : 0 ≤ b) :
    B.gN (x⁻¹ * A * y) ^ (-b) ≤ (B.gN x * B.gN y) ^ b * B.gN A ^ (-b) := by sorry
