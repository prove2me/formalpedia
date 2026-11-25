-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormSums_herm_rsum
-- name    : Formalism.FourierDecayAlt.P.HermitianFormSums.herm_rsum
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:21:06.741412+00:00
-- url     : https://prove2.me/theorems/c2fc960d-9bbd-508d-a40a-22bfa5066f8d
-- title:
--   Hermitian Form Sums: herm rsum
-- statement:
--   The Hermitian Form Sums construction uses the herm rsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameCompletion.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameCompletion.lean#L24-L29

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

theorem Formalism.FourierDecayAlt.P.HermitianFormSums.herm_rsum {N : ℕ} {ι : Type*} (H : Matrix (Fin N) (Fin N) ℂ) (s : Finset ι) (c : ι → ℂ) (v : ι → Fin N → ℂ)
    (w : Fin N → ℂ) : herm H w (∑ a ∈ s, c a • v a) = ∑ a ∈ s, star (c a) * herm H w (v a) := by sorry
