-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_harm_eq_NF
-- name    : Formalism.FourierDecayAlt.P.Sz3.harm_eq_NF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:43.198798+00:00
-- url     : https://prove2.me/theorems/bd67a06c-2460-4cbd-9f2c-4f29bdb4a521
-- title:
--   Sz3: harm eq NF
-- statement:
--   The Sz3 construction uses the harm eq NF property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L208-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L208-L221

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

theorem Formalism.FourierDecayAlt.P.Sz3.harm_eq_NF (J : ℕ) (de : ℕ → ℝ) :
    ∑ i ∈ Icc 1 J, de i * (((harmonic (i - 1) : ℚ) : ℝ) - ((harmonic (J - i) : ℚ) : ℝ)) =
      NF J de := by sorry
