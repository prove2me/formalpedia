-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_ratio_exp
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.ratio_exp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:02:12.73269+00:00
-- url     : https://prove2.me/theorems/425d384f-7427-4dc6-8b5a-89136438ab3a
-- title:
--   Gauge R: ratio exp
-- statement:
--   The Gauge R construction uses the ratio exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqC.lean#L92-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqC.lean#L92-L161

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqC
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB
open Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {H : Host E} {Dw : Datum H} {l : Level H}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.ratio_exp (hR : GaugeRatioSt) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (r : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (h1 : MvPowerSeries.constantCoeff r = 1)
    (hr : ∀ a : 𝓞 E, MvPowerSeries.rescale (sc (Dw := Dw) c S (1 + a * H.bar a)) r =
      MvPowerSeries.rescale (sc (Dw := Dw) c S a) r ^ 2 * r * MvPowerSeries.rescale (sc (Dw := Dw) c S (a * H.bar a)) r) :
    ∃ q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S, MvPowerSeries.constantCoeff q = 0 ∧
      (∀ m, MvPowerSeries.coeff m q ≠ 0 → m.degree = 2) ∧
      (∀ ℓ ℓ' : Lt1 Dw, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ) 1 +
          Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ') 1) q ≠ 0 → ℓ'.1 = ComplexEmbedding.conjugate ℓ.1) ∧
      r = PowerSeries.subst q (PowerSeries.exp S) := by sorry
