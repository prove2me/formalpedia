-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_exp_pow_eq
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.exp_pow_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:01:01.622893+00:00
-- url     : https://prove2.me/theorems/ac21d2f4-98f0-44c7-b6dd-f6453ae6227b
-- title:
--   Gauge R: exp pow eq
-- statement:
--   The Gauge R construction uses the exp pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeExpPow.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeExpPow.lean#L15-L21

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeExpPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.exp_pow_eq {S σ : Type} [CommRing S] [Algebra ℚ S] (q : MvPowerSeries σ S)
    (hq : MvPowerSeries.constantCoeff q = 0) : ∀ k : ℕ,
    PowerSeries.subst q (PowerSeries.exp S) ^ k = PowerSeries.subst ((k : S) • q) (PowerSeries.exp S)
  := by sorry
