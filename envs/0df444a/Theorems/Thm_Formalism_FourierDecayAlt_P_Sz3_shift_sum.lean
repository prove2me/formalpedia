-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_shift_sum
-- name    : Formalism.FourierDecayAlt.P.Sz3.shift_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:14.369111+00:00
-- url     : https://prove2.me/theorems/5e757f84-585d-4a15-8153-14097e96fa74
-- title:
--   Sz3: shift sum
-- statement:
--   The Sz3 construction uses the shift sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L176-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L176-L183

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

theorem Formalism.FourierDecayAlt.P.Sz3.shift_sum (J d : ℕ) (hd : d ≤ J) (de : ℕ → ℝ) :
    ∑ i ∈ Icc 1 (J - d), de (i + d) = ∑ i ∈ Ioc d J, de i := by sorry
