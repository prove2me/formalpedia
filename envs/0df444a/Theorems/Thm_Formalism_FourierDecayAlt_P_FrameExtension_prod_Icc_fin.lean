-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FrameExtension_prod_Icc_fin
-- name    : Formalism.FourierDecayAlt.P.FrameExtension.prod_Icc_fin
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:09:20.033788+00:00
-- url     : https://prove2.me/theorems/ba67721c-17e3-478e-a958-b9a0f34ea09b
-- title:
--   Frame Extension: prod Icc fin
-- statement:
--   The Frame Extension construction uses the prod Icc fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameExtension.lean#L73-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameExtension.lean#L73-L78

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FrameExtension
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.FrameExtension.prod_Icc_fin (n : ℕ) (f : ℕ → ℂ) : ∏ i ∈ Finset.Icc 1 (n + 1), f i = ∏ j : Fin (n + 1), f ((j : ℕ) + 1) := by sorry
