-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormRankFour_mul_colM
-- name    : Formalism.FourierDecayAlt.P.HermitianFormRankFour.mul_colM
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:06:44.69745+00:00
-- url     : https://prove2.me/theorems/ebf6463f-263f-554f-89ae-c1b87a958fca
-- title:
--   Hermitian Form Rank Four: mul col M
-- statement:
--   The Hermitian Form Rank Four construction uses the mul col M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean#L147-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean#L147-L147

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

theorem Formalism.FourierDecayAlt.P.HermitianFormRankFour.mul_colM (h : Matrix N N ℂ) (U : J → N → ℂ) : h * colM U = colM fun j => h *ᵥ U j := by sorry
