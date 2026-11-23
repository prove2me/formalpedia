-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_diff_bd
-- name    : Formalism.FourierDecayAlt.P.Sz3.diff_bd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:46.083186+00:00
-- url     : https://prove2.me/theorems/49d54be7-e7c9-4368-826a-3dc09d0f802f
-- title:
--   Sz3: diff bd
-- statement:
--   The Sz3 construction uses the diff bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L286-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L286-L305

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

theorem Formalism.FourierDecayAlt.P.Sz3.diff_bd (J d : ℕ) (hd : d ≤ J) (de : ℕ → ℝ) (hde : ∀ i, de i = 0 ∨ de i = 1) :
    |∑ i ∈ Ioc d J, de i - ∑ i ∈ Icc 1 (J - d), de i| ≤ (d : ℝ) ∧
    |∑ i ∈ Ioc d J, de i - ∑ i ∈ Icc 1 (J - d), de i| ≤ (J : ℝ) - (d : ℝ) := by sorry
