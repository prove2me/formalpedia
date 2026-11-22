-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ChainAndRowSums_cm_two
-- name    : Formalism.FourierDecayAlt.P.ChainAndRowSums.cm_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:20.694112+00:00
-- url     : https://prove2.me/theorems/5d53f05a-2342-455b-a1a3-b95bddb06c3b
-- title:
--   Chain And Row Sums: cm two
-- statement:
--   The Chain And Row Sums construction uses the cm two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainAndRowSums.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainAndRowSums.lean#L11-L13

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainAndRowSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ChainAndRowSums
open Formalism.FourierDecayAlt.crystallineComparison

theorem Formalism.FourierDecayAlt.P.ChainAndRowSums.cm_two {W : Type} (Wd : Finset W) (c : ℕ → W → W → ℝ) (k : ℕ) (w w'' : W) :
    chainMat Wd c (k + 2) w w'' = ∑ w' ∈ Wd, c (k + 2) w w' * chainMat Wd c (k + 1) w' w'' := by sorry
