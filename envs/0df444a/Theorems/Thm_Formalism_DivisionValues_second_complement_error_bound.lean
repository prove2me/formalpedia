-- Prove2me | Theorems.Thm_Formalism_DivisionValues_second_complement_error_bound
-- name    : Formalism.DivisionValues.second_complement_error_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:43.044838+00:00
-- url     : https://prove2.me/theorems/2a856571-6607-42ee-abb2-0852993c4dad
-- title:
--   Division Values: second complement error bound
-- statement:
--   The Division Values construction uses the second complement error bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L419-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L419-L428

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

theorem Formalism.DivisionValues.second_complement_error_bound (C0 f N tt m η b w'' er : ℝ) (hC0 : 0 ≤ C0) (hf : 1 ≤ f) (hm : 1 ≤ m)
    (hNN : N * (N + tt) ≤ b) (hmη : m * η ≤ w'') (hwb : w'' ≤ b)
    (her : er ≤ C0 * (f * (N * (N + tt) + m ^ 2 * η))) : er ≤ C0 * (f * (b + m * b)) := by sorry
