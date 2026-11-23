-- Prove2me | Theorems.Thm_Formalism_L2_Pj_frMap_cancel
-- name    : Formalism.L2.Pj.frMap_cancel
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:59:46.974308+00:00
-- url     : https://prove2.me/theorems/dfffe40a-559c-4a87-8e39-76cf1e66e34a
-- title:
--   Pj: fr Map cancel
-- statement:
--   The Pj construction uses the fr Map cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/FrameCharts.lean#L164-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/FrameCharts.lean#L164-L200

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {c : Coeff l}

theorem Formalism.L2.Pj.frMap_cancel : MapCancel (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) := by sorry
