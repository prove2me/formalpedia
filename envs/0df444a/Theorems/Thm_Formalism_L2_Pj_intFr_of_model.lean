-- Prove2me | Theorems.Thm_Formalism_L2_Pj_intFr_of_model
-- name    : Formalism.L2.Pj.intFr_of_model
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:13.014341+00:00
-- url     : https://prove2.me/theorems/c3cc4fb5-8457-4140-82a4-e6b1ec9dc957
-- title:
--   Pj: int Fr of model
-- statement:
--   The Pj construction uses the int Fr of model property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RealPtGeo.lean#L17-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RealPtGeo.lean#L17-L34

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntFrames
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ExtPtUnique
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RealPtGeo
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem Formalism.L2.Pj.intFr_of_model (hIF : IntFramesSt Xo c) (T : CDVR) (io : c.F →+* T.Fr) {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β) (hPI : PushInvertible Y.t.G Y.t.PP.L) (b : O →+* T.V)
    (hb : (algebraMap T.V T.Fr).comp b = io.comp β) (y₀ : letI := io.toAlgebra; FrPt Xo c T.Fr) :
    ∃ (y : IntFr Xo c T io) (t : Ix Dw → T.Frˣ), (letI := io.toAlgebra; FrBor t y₀ y.1) := by sorry
