-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_pair_eq_NF
-- name    : Formalism.FourierDecayAlt.P.Sz3.pair_eq_NF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:13.371785+00:00
-- url     : https://prove2.me/theorems/434031bb-ad98-4daf-8292-c5c20d59daa7
-- title:
--   Sz3: pair eq NF
-- statement:
--   The Sz3 construction uses the pair eq NF property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L185-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L185-L201

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

theorem Formalism.FourierDecayAlt.P.Sz3.pair_eq_NF (J : ℕ) (de : ℕ → ℝ) :
    ∑ i ∈ Icc 1 J, ∑ i' ∈ Ioc i J, (de i' - de i) / (4 * ((i' : ℝ) - (i : ℝ))) =
      (1 / 4) * NF J de := by sorry
