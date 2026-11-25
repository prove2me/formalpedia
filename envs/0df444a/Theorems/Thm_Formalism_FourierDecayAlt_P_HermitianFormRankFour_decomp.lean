-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormRankFour_decomp
-- name    : Formalism.FourierDecayAlt.P.HermitianFormRankFour.decomp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:10:19.698269+00:00
-- url     : https://prove2.me/theorems/4a40b5f2-1260-46fe-84f6-05b752d6966e
-- title:
--   Hermitian Form Rank Four: decomp
-- statement:
--   The Hermitian Form Rank Four construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean#L127-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean#L127-L136

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

theorem Formalism.FourierDecayAlt.P.HermitianFormRankFour.decomp (hc : V * Vd + C * Cd = 1) (h3 : Cd * V = 0) (h : Matrix N N ℂ) (hC : h * C = C) (hCd : Cd * h = Cd) :
    h * V = V * (Vd * h * V) ∧ h = V * (Vd * h * V) * Vd + C * Cd := by sorry
