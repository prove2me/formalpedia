-- Prove2me | Theorems.Thm_Formalism_DivisionValues_second_complement_absorption
-- name    : Formalism.DivisionValues.second_complement_absorption
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:30.479788+00:00
-- url     : https://prove2.me/theorems/c015afdf-d34b-42e1-9615-baa6d8bb2814
-- title:
--   Division Values: second complement absorption
-- statement:
--   The Division Values construction uses the second complement absorption property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L452-L472
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L452-L472

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
noncomputable section
open Formalism Formalism.DivisionValues
open PlaceSumConjugation

theorem Formalism.DivisionValues.second_complement_absorption (W' Dl er lg Eels C0 f m b L B0 : ℝ) (hB0 : B0 = f * m * b * L) (hf : 1 ≤ f)
    (hm : 1 ≤ m) (hb : 0 ≤ b) (hC0 : 0 ≤ C0) (hfbL : f * b * L ≤ B0)
    (hW : W' ≤ f * (2 * b)) (hDl : Dl ≤ f * (5 * C0 * b)) (her : er ≤ C0 * (f * (b + m * b)))
    (hlg0 : 0 ≤ lg) (hlg : lg ≤ C0 * L) (hE : Eels ≤ (2 * C0 + 10) * B0) :
    (W' + Dl + 2 * er) * lg + 2 * Eels ≤ (9 * C0 ^ 2 + 6 * C0 + 20) * B0 := by sorry
