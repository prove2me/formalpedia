-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_psIn_succ_sub
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.psIn_succ_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:17.545891+00:00
-- url     : https://prove2.me/theorems/e9491b35-0d0c-4fd8-9cad-78cbeb98964d
-- title:
--   Germ B: ps In succ sub
-- statement:
--   The Germ B construction uses the ps In succ sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermBSer.lean#L62-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermBSer.lean#L62-L106

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBFr
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] {κ κ' : Type}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.psIn_succ_sub {d n n' : ℕ} (m : ℕ) (r : Fin n → Fin n') (g : MvPowerSeries (Fin n × Fin d) S) :
    psIn d (m + 1) r g - psIn d m r g ∈ orig S (Fin n' × Fin d) ^ (m + 1) := by sorry
