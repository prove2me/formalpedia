-- Prove2me | Theorems.Thm_Formalism_L2_Pj_fnFG_of
-- name    : Formalism.L2.Pj.fnFG_of
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:21:52.257252+00:00
-- url     : https://prove2.me/theorems/e73495ec-35b9-4df0-9609-d46d69e85092
-- title:
--   Pj: fn FG of
-- statement:
--   The Pj construction uses the fn FG of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/FnTrdegOf.lean#L17-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/FnTrdegOf.lean#L17-L61

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompHt
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FnTrdegOf
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
  (Xo : Moduli Dw l) (c : Coeff l)

theorem Formalism.L2.Pj.fnFG_of (h : KapFG Xo c) : FnFG Xo c := by sorry
