-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormRankFour_exp_semiconj
-- name    : Formalism.FourierDecayAlt.P.HermitianFormRankFour.exp_semiconj
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:23:38.457949+00:00
-- url     : https://prove2.me/theorems/60633f03-9513-5841-aa92-54fb23e1a13a
-- title:
--   Hermitian Form Rank Four: exp semiconj
-- statement:
--   The Hermitian Form Rank Four construction uses the exp semiconj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean#L83-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean#L83-L104

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
variable {N K J : Type} [Fintype N] [Fintype K] [Fintype J] [DecidableEq N] [DecidableEq K] [DecidableEq J]

theorem Formalism.FourierDecayAlt.P.HermitianFormRankFour.exp_semiconj (X : Matrix N N ℂ) (B : Matrix K K ℂ) (V : Matrix N K ℂ) (h : X * V = V * B) :
    NormedSpace.exp X * V = V * NormedSpace.exp B := by sorry
