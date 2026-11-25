-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormRankFour_exists_theta
-- name    : Formalism.FourierDecayAlt.P.HermitianFormRankFour.exists_theta
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:07:19.320351+00:00
-- url     : https://prove2.me/theorems/914a0401-97aa-567e-9baa-119577120600
-- title:
--   Hermitian Form Rank Four: exists theta
-- statement:
--   The Hermitian Form Rank Four construction uses the exists theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean#L17-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean#L17-L31

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormRankFour
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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD
open Formalism.FourierDecayAlt.P.HermitianFormRankFour
open scoped Matrix.Norms.L2Operator

theorem Formalism.FourierDecayAlt.P.HermitianFormRankFour.exists_theta {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ∃ θ : ℝ, -Complex.exp (θ * Complex.I) ∉ spectrum ℂ A := by sorry
