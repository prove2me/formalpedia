-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ChainAndRowSums_cm_nonneg
-- name    : Formalism.FourierDecayAlt.P.ChainAndRowSums.cm_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:34.332672+00:00
-- url     : https://prove2.me/theorems/8fd5b770-cadf-48d2-9a3a-0f37be6a3f2e
-- title:
--   Chain And Row Sums: cm nonneg
-- statement:
--   The Chain And Row Sums construction uses the cm nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainAndRowSums.lean#L51-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainAndRowSums.lean#L51-L64

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

theorem Formalism.FourierDecayAlt.P.ChainAndRowSums.cm_nonneg {W : Type} (Wd : Finset W) (c : ℕ → W → W → ℝ) (hc : ∀ n w w', 0 ≤ c n w w') :
    ∀ n w w', 0 ≤ chainMat Wd c n w w' := by sorry
