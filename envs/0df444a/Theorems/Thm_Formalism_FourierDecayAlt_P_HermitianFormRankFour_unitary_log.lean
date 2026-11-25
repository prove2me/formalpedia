-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormRankFour_unitary_log
-- name    : Formalism.FourierDecayAlt.P.HermitianFormRankFour.unitary_log
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:11:19.024294+00:00
-- url     : https://prove2.me/theorems/a5ea4a04-8044-5af5-b772-ad29bd6fd01f
-- title:
--   Hermitian Form Rank Four: unitary log
-- statement:
--   The Hermitian Form Rank Four construction uses the unitary log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean#L76-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean#L76-L77

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

theorem Formalism.FourierDecayAlt.P.HermitianFormRankFour.unitary_log {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (hA : Aᴴ * A = 1) :
    ∃ B : Matrix (Fin k) (Fin k) ℂ, Bᴴ = -B ∧ NormedSpace.exp B = A := by sorry
