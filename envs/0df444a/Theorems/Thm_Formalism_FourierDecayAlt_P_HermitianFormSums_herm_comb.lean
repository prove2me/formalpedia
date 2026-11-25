-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormSums_herm_comb
-- name    : Formalism.FourierDecayAlt.P.HermitianFormSums.herm_comb
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:37:56.812796+00:00
-- url     : https://prove2.me/theorems/79e5a0d7-eb1c-48da-805d-3562b9abd65f
-- title:
--   Hermitian Form Sums: herm comb
-- statement:
--   The Hermitian Form Sums construction uses the herm comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameCompletion.lean#L41-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameCompletion.lean#L41-L48

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameCompletion
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
open Formalism.FourierDecayAlt.P.HermitianFormSums
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.HermitianFormSums.herm_comb {m : ℕ} {vs : List (Fin (2 * r + k + 1) → ℂ)} {C : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hC : IsFrameOf k r vs C) (f g : Fin m → ℂ) :
    herm (Hpk k r) (∑ a, f a • C a) (∑ b, g b • C b) = ∑ a, f a * star (g a) := by sorry
