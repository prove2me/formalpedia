-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormRankFour_skew_of
-- name    : Formalism.FourierDecayAlt.P.HermitianFormRankFour.skew_of
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:14:37.118101+00:00
-- url     : https://prove2.me/theorems/ccf3e5f7-2a22-5c71-b65e-964dc153207f
-- title:
--   Hermitian Form Rank Four: skew of
-- statement:
--   The Hermitian Form Rank Four construction uses the skew of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean#L166-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean#L166-L168

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
variable {V : Matrix N K ℂ} {C : Matrix N J ℂ} {Vd : Matrix K N ℂ} {Cd : Matrix J N ℂ}

theorem Formalism.FourierDecayAlt.P.HermitianFormRankFour.skew_of {H : Matrix N N ℂ} (hH : Hᴴ = H) {B : Matrix K K ℂ} (hB : Bᴴ = -B) :
    (V * B * (Vᴴ * H))ᴴ * H + H * (V * B * (Vᴴ * H)) = 0 := by sorry
