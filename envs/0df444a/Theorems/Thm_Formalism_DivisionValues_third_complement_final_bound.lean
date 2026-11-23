-- Prove2me | Theorems.Thm_Formalism_DivisionValues_third_complement_final_bound
-- name    : Formalism.DivisionValues.third_complement_final_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:03.389348+00:00
-- url     : https://prove2.me/theorems/9538161b-3674-453d-8e3a-846ecda7afae
-- title:
--   Division Values: third complement final bound
-- statement:
--   The Division Values construction uses the third complement final bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L629-L711
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L629-L711

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

theorem Formalism.DivisionValues.third_complement_final_bound (C0 c a La m B0 f b L S Sc η N k w'' b' Δ tt P1 P1' MM TTm cPl : ℝ)
    (hB0 : B0 = f * m * b * L) (hf : 1 ≤ f) (hm : 1 ≤ m) (hL1 : 1 ≤ L) (hb : 0 ≤ b)
    (hc0 : 0 ≤ c) (ha : 0 ≤ a) (hLLa : L ≤ La) (hLa3 : La ≤ 3 * L) (hk : 1 ≤ k) (hN : 1 ≤ N)
    (hS : 0 ≤ S) (hSc : Sc ≤ 3 * S) (htt : 0 ≤ tt) (hη : 0 ≤ η) (hb' : 0 ≤ b')
    (hcPl0 : 0 ≤ cPl) (hcPl : cPl ≤ f)
    (h3 : m ^ 3 * N ^ 2 * L ≤ b) (hkN : k * N ≤ b) (hkS : k * S ≤ w'')
    (hmη : m * (tt + 1) * η ≤ w'') (hNw : N * w'' ≤ b) (hmkb : m * k * b' ≤ a) (hmΔ : m * Δ ≤ a)
    (hP1 : |P1| ≤ C0 * (c * b' + cPl * (S + m * η + N)) * (C0 * m * L))
    (hP1' : |P1'| ≤ C0 * (c * b' + cPl * (S + m * η + N)) * (C0 * m * L))
    (hMM : |MM| ≤ m * (cPl * (2 * (k * Sc * La)) + c * (2 * (Δ * La))))
    (hT : |TTm| ≤ m * (C0 * (f * m ^ 2 * N ^ 2)) * (C0 * m * L)) :
    |P1 - P1' + MM + TTm| ≤ (7 * C0 ^ 2 + 18) * (c * a * La + m * B0) := by sorry
