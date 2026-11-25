-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermRateSplit_sum_sq_le_sq_sum
-- name    : Formalism.FourierDecayAlt.P.GermRateSplit.sum_sq_le_sq_sum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:53:08.089321+00:00
-- url     : https://prove2.me/theorems/108dbc12-fe2b-5836-abbd-6073ef71c66f
-- title:
--   Germ Rate Split: sum sq le sq sum
-- statement:
--   The Germ Rate Split construction uses the sum sq le sq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormSumLeOfGram.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormSumLeOfGram.lean#L19-L24

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormSumLeOfGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermRateSplit
open Finset
open scoped ComplexConjugate InnerProductSpace

theorem Formalism.FourierDecayAlt.P.GermRateSplit.sum_sq_le_sq_sum {I : Type} [Fintype I] (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∑ i, x i ^ 2 ≤ (∑ i, x i) ^ 2 := by sorry
