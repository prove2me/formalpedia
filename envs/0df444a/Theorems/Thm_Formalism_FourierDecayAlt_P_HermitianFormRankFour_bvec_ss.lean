-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormRankFour_bvec_ss
-- name    : Formalism.FourierDecayAlt.P.HermitianFormRankFour.bvec_ss
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:19:27.503981+00:00
-- url     : https://prove2.me/theorems/ab70bfcd-fa16-593a-b3f8-c9ab9efc4548
-- title:
--   Hermitian Form Rank Four: bvec ss
-- statement:
--   The Hermitian Form Rank Four construction uses the bvec ss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean#L218-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean#L218-L222

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
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.HermitianFormRankFour.bvec_ss (c c' : Fin r) : bvec (esI k r c') (esI k r c) = if c = c' then 1 else 0 := by sorry
