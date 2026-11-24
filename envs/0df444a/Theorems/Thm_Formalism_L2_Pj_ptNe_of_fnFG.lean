-- Prove2me | Theorems.Thm_Formalism_L2_Pj_ptNe_of_fnFG
-- name    : Formalism.L2.Pj.ptNe_of_fnFG
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:22:48.572871+00:00
-- url     : https://prove2.me/theorems/0655a526-7752-4054-a11a-5b975df87ded
-- title:
--   Pj: pt Ne of fn FG
-- statement:
--   The Pj construction uses the pt Ne of fn FG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AxHSup.lean#L30-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AxHSup.lean#L30-L30

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompHt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PTNonempty
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AxHSup
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
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]

theorem Formalism.L2.Pj.ptNe_of_fnFG (hfg : FnFG Xo c) : PTNe Xo c := by sorry
