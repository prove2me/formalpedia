-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormSums_sum_mdim
-- name    : Formalism.FourierDecayAlt.P.HermitianFormSums.sum_mdim
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:07:10.675804+00:00
-- url     : https://prove2.me/theorems/d72b0699-6e01-57c2-9a3f-2c2b30ec8c38
-- title:
--   Hermitian Form Sums: sum mdim
-- statement:
--   The Hermitian Form Sums construction uses the sum mdim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameCompletion.lean#L50-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameCompletion.lean#L50-L52

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

theorem Formalism.FourierDecayAlt.P.HermitianFormSums.sum_mdim {X : Type*} [AddCommMonoid X] (F : ℕ → X) :
    ∑ j : Fin (mdim k r (Fin.last r)), F j.val = ∑ a : Fin k, F a.val + F k := by sorry
