-- Prove2me | Theorems.Thm_Formalism_L2_Pj_dualMap_alg
-- name    : Formalism.L2.Pj.dualMap_alg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:53.597095+00:00
-- url     : https://prove2.me/theorems/0aced423-1179-4e14-9984-8d45d060053f
-- title:
--   Pj: dual Map alg
-- statement:
--   The Pj construction uses the dual Map alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/FrameCharts.lean#L247-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/FrameCharts.lean#L247-L250

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnitIndepOfCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open MonObj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem Formalism.L2.Pj.dualMap_alg {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    (dualMap φ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp φ := by sorry
