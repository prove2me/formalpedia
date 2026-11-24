-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_pull_restrict_unit_value
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.pull_restrict_unit_value
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:02:35.291107+00:00
-- url     : https://prove2.me/theorems/cc93181c-c694-4cd0-ac23-b635556c8dc5
-- title:
--   H1: pull restrict unit value
-- statement:
--   The H1 construction uses the pull restrict unit value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PrimUniqPf.lean#L83-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PrimUniqPf.lean#L83-L87

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqPf
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
open AlgebraicGeometry CategoryTheory NumberField TopologicalSpace Opposite MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.pull_restrict_unit_value {X Y : Scheme.{0}} (h : Y ⟶ X) {V : X.Opens} {W W' : Y.Opens} (hWV : W ≤ h ⁻¹ᵁ V)
    (hW' : W' ≤ W) (u : Γ(X, ⊤)ˣ) :
    ((res hW' (res hWV (pullU h V (res (le_top : V ≤ ⊤) u))) : Γ(Y, W')ˣ) : Γ(Y, W')) =
      (Y.presheaf.map (homOfLE (le_top : W' ≤ h ⁻¹ᵁ ⊤)).op).hom ((h.app ⊤).hom (u : Γ(X, ⊤))) := by sorry
