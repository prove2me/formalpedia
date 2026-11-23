-- Prove2me | Theorems.Thm_Formalism_L2_Pj_exZ_add
-- name    : Formalism.L2.Pj.exZ_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:15:47.8658+00:00
-- url     : https://prove2.me/theorems/e9c45b17-6425-4429-8c8f-fc79a67085f0
-- title:
--   Pj: ex Z add
-- statement:
--   The Pj construction uses the ex Z add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompOrd.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompOrd.lean#L16-L17

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompData
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompOrd
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
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem Formalism.L2.Pj.exZ_add (G G' : WTZ E) (i : Ix Dw) : exZ Dw (G + G') i = exZ Dw G i + exZ Dw G' i := by sorry
