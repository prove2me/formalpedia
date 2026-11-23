-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_PeriodAreaSignLemmas_altE_coord
-- name    : Formalism.L2.Th1.F.PeriodAreaSignLemmas.altE_coord
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:43:07.203596+00:00
-- url     : https://prove2.me/theorems/3a8b380b-15d0-4503-a46d-383d3ef89139
-- title:
--   Period Area Sign Lemmas: alt E coord
-- statement:
--   The Period Area Sign Lemmas construction uses the alt E coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/QuasiPeriodConstUniqueOf.lean#L123-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/QuasiPeriodConstUniqueOf.lean#L123-L135

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstUniqueOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open PeriodAreaSignLemmas
open Formalism.L2.Th1.F.PeriodAreaSignLemmas

theorem Formalism.L2.Th1.F.PeriodAreaSignLemmas.altE_coord (L : PeriodPair) (m n m' n' : ℤ) :
    altE L ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ((m' : ℂ) * L.ω₁ + (n' : ℂ) * L.ω₂)
      = ((-(sgn L * (m * n' - n * m')) : ℤ) : ℝ) := by sorry
