-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SkewHermitianParts_pow_mem
-- name    : Formalism.FourierDecayAlt.P.SkewHermitianParts.pow_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:20:31.836418+00:00
-- url     : https://prove2.me/theorems/af027fe4-5b3b-5e0d-a588-cf3704f8bfc3
-- title:
--   Skew Hermitian Parts: pow mem
-- statement:
--   The Skew Hermitian Parts construction uses the pow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExistsFrameTwo.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExistsFrameTwo.lean#L27-L33

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExistsFrameTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.SkewHermitianParts
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

theorem Formalism.FourierDecayAlt.P.SkewHermitianParts.pow_mem (S : Submodule ℂ W) {A : W →L[ℂ] W} (hA : ∀ v ∈ S, A v ∈ S) (n : ℕ) : ∀ v ∈ S, (A ^ n) v ∈ S := by sorry
