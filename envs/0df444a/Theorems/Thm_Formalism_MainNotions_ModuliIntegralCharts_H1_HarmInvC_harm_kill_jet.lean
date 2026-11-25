-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_HarmInvC_harm_kill_jet
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC.harm_kill_jet
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:03:01.882446+00:00
-- url     : https://prove2.me/theorems/db1d6643-0bb6-45d0-808a-72afb1ef87c1
-- title:
--   Harm Inv C: harm kill jet
-- statement:
--   The Harm Inv C construction uses the harm kill jet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HarmInvC.lean#L89-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HarmInvC.lean#L89-L160

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffPolyAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PsiCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_KillAddFin
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvC
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC.harm_kill_jet {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] (k n D : ℕ)
    (g g' : Fin n → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (β : Matrix (Fin (dL Dw)) (Fin (dL Dw)) S)
    (hβ : ∀ i j, β i j ≠ 0 → ((ltIdx Dw).symm j).1 = ComplexEmbedding.conjugate ((ltIdx Dw).symm i).1)
    (hj : ∀ b, psJet D (g' b) =
      psJet D (g b * PowerSeries.subst ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) β) (PowerSeries.exp S)))
    (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmA c a n)
    (hD : ∀ m ∈ P.support, m.degree ≤ D) :
    ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g' b) (colOf m b) =
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g b) (colOf m b) := by sorry
