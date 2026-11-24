-- Prove2me | Theorems.Thm_Formalism_L2_Pj_isPrim_iff
-- name    : Formalism.L2.Pj.isPrim_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:09.52319+00:00
-- url     : https://prove2.me/theorems/3eed09ad-bc7d-4a63-bda6-9d9fc4d95cea
-- title:
--   Pj: is Prim iff
-- statement:
--   The Pj construction uses the is Prim iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IsChartIff.lean#L178-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IsChartIff.lean#L178-L178

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

theorem Formalism.L2.Pj.isPrim_iff (wP : PrimTy H Xo) : IsPrim wP ↔ IsPrimG Xo.univ.t wP := by sorry
