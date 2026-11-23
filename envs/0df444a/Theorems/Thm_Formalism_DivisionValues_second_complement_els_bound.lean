-- Prove2me | Theorems.Thm_Formalism_DivisionValues_second_complement_els_bound
-- name    : Formalism.DivisionValues.second_complement_els_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:35.432794+00:00
-- url     : https://prove2.me/theorems/1bf459f3-b791-453a-bd99-64238495e9ad
-- title:
--   Division Values: second complement els bound
-- statement:
--   The Division Values construction uses the second complement els bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L430-L450
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L430-L450

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

theorem Formalism.DivisionValues.second_complement_els_bound (C0 B0 f b L k b' N X'' logd c Eels : ℝ) (hC0 : 0 ≤ C0) (hf : 1 ≤ f) (hb : 0 ≤ b)
    (hk : 1 ≤ k) (hb' : 0 ≤ b') (hc : c ≤ f) (hkb : k * b' ≤ b)
    (hX : f * k * N * X'' ≤ b) (hd0 : 0 ≤ logd) (hd : logd ≤ L) (hfbL : f * b * L ≤ B0)
    (hbB0 : b ≤ B0)
    (hE : Eels ≤ C0 * B0 + (c * (2 * b + 4 * k * b') + 4 * f * k * b') * logd +
      C0 * (f * k * N * X'')) : Eels ≤ (2 * C0 + 10) * B0 := by sorry
