-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormRankFour_gramM_apply
-- name    : Formalism.FourierDecayAlt.P.HermitianFormRankFour.gramM_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:11:31.855801+00:00
-- url     : https://prove2.me/theorems/a7bd6cf7-b8e8-47f0-a326-baa1be996bc7
-- title:
--   Hermitian Form Rank Four: gram M apply
-- statement:
--   The Hermitian Form Rank Four construction uses the gram M apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean#L140-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean#L140-L145

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

theorem Formalism.FourierDecayAlt.P.HermitianFormRankFour.gramM_apply (H : Matrix N N ℂ) (U : J → N → ℂ) (W : K → N → ℂ) (i : J) (j : K) :
    ((colM U)ᴴ * H * colM W) i j = herm H (W j) (U i) := by sorry
