-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormSums_herm_lsum
-- name    : Formalism.FourierDecayAlt.P.HermitianFormSums.herm_lsum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:26:46.147167+00:00
-- url     : https://prove2.me/theorems/174bce9e-df29-5e00-9bc5-c86f6174284b
-- title:
--   Hermitian Form Sums: herm lsum
-- statement:
--   The Hermitian Form Sums construction uses the herm lsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameCompletion.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameCompletion.lean#L17-L22

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

theorem Formalism.FourierDecayAlt.P.HermitianFormSums.herm_lsum {N : ℕ} {ι : Type*} (H : Matrix (Fin N) (Fin N) ℂ) (s : Finset ι) (c : ι → ℂ) (v : ι → Fin N → ℂ)
    (w : Fin N → ℂ) : herm H (∑ a ∈ s, c a • v a) w = ∑ a ∈ s, c a * herm H (v a) w := by sorry
