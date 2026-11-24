-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_expAct_core
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.expAct_core
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:02:29.286344+00:00
-- url     : https://prove2.me/theorems/9a2d92b5-8dff-43b0-acb0-cbf53bd5caa7
-- title:
--   H1: exp Act core
-- statement:
--   The H1 construction uses the exp Act core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpActPf.lean#L102-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpActPf.lean#L102-L238

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpAct
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpActPf
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ExpTieAlg ExpActPf
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.expAct_core {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {S : Type}
    [CommRing S] [Algebra ℚ S] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB S d O) (uvec : Lt1 Dw → Fin d → S)
    (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (hφ : IsExpOf B.G.F uvec φ) (a : O) (cA : Lt1 Dw → S)
    (hE : ∀ (ℓ : Lt1 Dw) (i : Fin d), ∑ j, dLin (B.A.act a) i j * uvec ℓ j = cA ℓ * uvec ℓ i) (j : Fin d) :
    subst (fam1 φ) (B.A.act a j) =
      subst (fun q : Fin 1 × Fin (dL Dw) => cA ((ltIdx Dw).symm q.2) • (X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S))
        (φ j) := by sorry
