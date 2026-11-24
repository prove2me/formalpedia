-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_KAV_coeff_prod_cols
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.KAV.coeff_prod_cols
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:01:59.098889+00:00
-- url     : https://prove2.me/theorems/45e3e02d-05c0-486b-87c1-0fbfc1a679c6
-- title:
--   KAV: coeff prod cols
-- statement:
--   The KAV construction uses the coeff prod cols property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ConstantCoeffPolyAdd.lean#L278-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ConstantCoeffPolyAdd.lean#L278-L339

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEncPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsExpChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffPolyAdd
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
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
open MvPowerSeries

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.KAV.coeff_prod_cols {S : Type} [CommRing S] {n d : ℕ} (g : Fin n → MvPowerSeries (Fin 1 × Fin d) S)
    (M : Fin n × Fin d →₀ ℕ) :
    coeff M (∏ b, rename (fun p : Fin 1 × Fin d => ((b, p.2) : Fin n × Fin d)) (g b)) =
      ∏ b, coeff (colPart b M) (g b) := by sorry
