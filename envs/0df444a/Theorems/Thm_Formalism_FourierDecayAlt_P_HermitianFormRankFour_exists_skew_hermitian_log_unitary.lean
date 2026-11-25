-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormRankFour_exists_skew_hermitian_log_unitary
-- name    : Formalism.FourierDecayAlt.P.HermitianFormRankFour.exists_skew_hermitian_log_unitary
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:13:00.331941+00:00
-- url     : https://prove2.me/theorems/b8e5ab47-f2bc-4a8a-bf06-feb546ac993e
-- title:
--   Hermitian Form Rank Four: exists skew hermitian log unitary
-- statement:
--   The Hermitian Form Rank Four construction uses the exists skew hermitian log unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean#L33-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean#L33-L72

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

theorem Formalism.FourierDecayAlt.P.HermitianFormRankFour.exists_skew_hermitian_log_unitary {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (hA : Aᴴ * A = 1) :
    ∃ B : Matrix (Fin k) (Fin k) ℂ, Bᴴ = -B ∧ NormedSpace.exp B = A := by sorry
