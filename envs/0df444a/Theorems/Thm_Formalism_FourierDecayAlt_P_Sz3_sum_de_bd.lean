-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_sum_de_bd
-- name    : Formalism.FourierDecayAlt.P.Sz3.sum_de_bd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:39.779828+00:00
-- url     : https://prove2.me/theorems/f35e9fd2-47be-42e5-a8b1-fb59c40ea449
-- title:
--   Sz3: sum de bd
-- statement:
--   The Sz3 construction uses the sum de bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L271-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L271-L281

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

theorem Formalism.FourierDecayAlt.P.Sz3.sum_de_bd (de : ℕ → ℝ) (hde : ∀ i, de i = 0 ∨ de i = 1) (s : Finset ℕ) :
    0 ≤ ∑ i ∈ s, de i ∧ ∑ i ∈ s, de i ≤ (s.card : ℝ) := by sorry
