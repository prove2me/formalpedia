-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_pair_reindex
-- name    : Formalism.FourierDecayAlt.P.Sz3.pair_reindex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:03.850149+00:00
-- url     : https://prove2.me/theorems/d833f68f-f560-4ac1-b051-2aef0af03a3e
-- title:
--   Sz3: pair reindex
-- statement:
--   The Sz3 construction uses the pair reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L154-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L154-L171

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz3
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz3.pair_reindex (J : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ i ∈ Icc 1 J, ∑ i' ∈ Ioc i J, f i i' = ∑ d ∈ Icc 1 J, ∑ i ∈ Icc 1 (J - d), f i (i + d) := by sorry
