-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_jetSubstP_trunc
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.jetSubstP_trunc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:34.347446+00:00
-- url     : https://prove2.me/theorems/6b1e9f65-c25c-4615-ab83-9c6bc5df01cb
-- title:
--   Germ B: jet Subst P trunc
-- statement:
--   The Germ B construction uses the jet Subst P trunc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermBSer.lean#L41-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermBSer.lean#L41-L48

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBFr
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.jetSubstP_trunc (m : ℕ) (φ : κ → MvPolynomial κ' S) :
    (jetTrunc : Jet S κ' (m + 1) →ₐ[S] Jet S κ' m).comp (jetSubstP (m + 1) φ) =
      (jetSubstP m φ).comp (jetTrunc : Jet S κ (m + 1) →ₐ[S] Jet S κ m) := by sorry
