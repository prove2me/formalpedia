-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormRankFour_unitary_of
-- name    : Formalism.FourierDecayAlt.P.HermitianFormRankFour.unitary_of
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:11:24.961807+00:00
-- url     : https://prove2.me/theorems/9134c64b-4f8c-5e0a-bf9a-0f55b58b2b7e
-- title:
--   Hermitian Form Rank Four: unitary of
-- statement:
--   The Hermitian Form Rank Four construction uses the unitary of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean#L155-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean#L155-L164

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

theorem Formalism.FourierDecayAlt.P.HermitianFormRankFour.unitary_of {H h : Matrix N N ℂ} (hH : Hᴴ = H) (hh : hᴴ * H * h = H) (h1 : Vᴴ * H * V = 1)
    (e1 : h * V = V * (Vᴴ * H * h * V)) : (Vᴴ * H * h * V)ᴴ * (Vᴴ * H * h * V) = 1 := by sorry
