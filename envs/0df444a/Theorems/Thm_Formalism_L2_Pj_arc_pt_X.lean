-- Prove2me | Theorems.Thm_Formalism_L2_Pj_arc_pt_X
-- name    : Formalism.L2.Pj.arc_pt_X
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:43.433306+00:00
-- url     : https://prove2.me/theorems/a9e4bd1b-bb39-45d0-8da1-7d954eb7964e
-- title:
--   Pj: arc pt X
-- statement:
--   The Pj construction uses the arc pt X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArcPtX.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArcPtX.lean#L24-L31

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArcPtX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem Formalism.L2.Pj.arc_pt_X (Dw : Datum H) (K₁ : Type) [Field K₁] (q : Sp (ArcS Dw K₁)) :
    PowerSeries.X ∉ ((spMap (arcι Dw K₁)) q).asIdeal := by sorry
