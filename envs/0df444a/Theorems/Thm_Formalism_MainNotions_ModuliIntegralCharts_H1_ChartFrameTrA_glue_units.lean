-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ChartFrameTrA_glue_units
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA.glue_units
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:59:33.374472+00:00
-- url     : https://prove2.me/theorems/e92c48ad-a2d7-41c4-aee4-c3399d338257
-- title:
--   Chart Frame Tr A: glue units
-- statement:
--   The Chart Frame Tr A construction uses the glue units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ChartFrameTrA.lean#L13-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ChartFrameTrA.lean#L13-L49

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartFrameTrA
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA.glue_units {X : Scheme.{0}} {κ : Type} (U : κ → X.Opens) (hcov : ∀ x : X, ∃ i, x ∈ U i)
    (r : ∀ i, Γ(X, U i)ˣ)
    (hr : ∀ i j, res (inf_le_left : U i ⊓ U j ≤ U i) (r i) = res (inf_le_right : U i ⊓ U j ≤ U j) (r j)) :
    ∃ u : Γ(X, ⊤)ˣ, ∀ i, res (le_top : U i ≤ ⊤) u = r i := by sorry
