-- Prove2me | Theorems.Thm_Formalism_L2_Pj_isChart_iff
-- name    : Formalism.L2.Pj.isChart_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:25.951732+00:00
-- url     : https://prove2.me/theorems/0e7eccbf-5ef6-4dd1-921a-bf35cdbbb87a
-- title:
--   Pj: is Chart iff
-- statement:
--   The Pj construction uses the is Chart iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IsChartIff.lean#L162-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IsChartIff.lean#L162-L167

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsChartIff
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
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open MvPolynomial (X C)
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
variable {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ)

theorem Formalism.L2.Pj.isChart_iff (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (uvec : Lt1 Dw → Fin d → S)
    (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G) :
    IsChart y d F act uvec x ↔ IsChartG Xo.univ.t y.x d F act (fun ℓ => y.u ℓ.1 ℓ.2) uvec x := by sorry
