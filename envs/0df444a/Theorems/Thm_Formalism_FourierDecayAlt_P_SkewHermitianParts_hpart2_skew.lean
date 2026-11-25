-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SkewHermitianParts_hpart2_skew
-- name    : Formalism.FourierDecayAlt.P.SkewHermitianParts.hpart2_skew
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:11:08.074649+00:00
-- url     : https://prove2.me/theorems/74cbf0bd-d88e-4d2b-a89a-ce83648b201e
-- title:
--   Skew Hermitian Parts: hpart2 skew
-- statement:
--   The Skew Hermitian Parts construction uses the hpart2 skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExistsFrameTwo.lean#L194-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExistsFrameTwo.lean#L194-L198

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExistsFrameTwo
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_hpart2_skew
import Theorems.Thm_QnYLeibnizW_hpart2_skew

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
open AnisotropicColumnSums
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.SkewHermitianParts.hpart2_skew {X : Mx k r} (hX : Xᴴ * Hpk k r + Hpk k r * X = 0) : hpart2 (Hpk k r) X = 0 := by sorry
