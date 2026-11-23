-- Prove2me | Theorems.Thm_Formalism_L2_Pj_extPt
-- name    : Formalism.L2.Pj.extPt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:45.898032+00:00
-- url     : https://prove2.me/theorems/7d210251-2973-447e-8349-f63b449ff4ea
-- title:
--   Pj: ext Pt
-- statement:
--   The Pj construction uses the ext Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ExtPtUnique.lean#L14-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ExtPtUnique.lean#L14-L26

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ExtPtUnique
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
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem Formalism.L2.Pj.extPt (Y : Model Xo c β) (T : CDVR) (b : O →+* T.V) (x : Sp T.Fr ⟶ Xo.XF c)
    (hx : x ≫ Y.j ≫ Y.s = Out.jK T.V ≫ spMap b) :
    ∃ yt : Sp T.V ⟶ Y.X, Out.jK T.V ≫ yt = x ≫ Y.j ∧ yt ≫ Y.s = spMap b := by sorry
