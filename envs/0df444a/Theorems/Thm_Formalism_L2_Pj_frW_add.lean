-- Prove2me | Theorems.Thm_Formalism_L2_Pj_frW_add
-- name    : Formalism.L2.Pj.frW_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:08.81138+00:00
-- url     : https://prove2.me/theorems/0ce3d287-17b5-475d-8d0e-4617c5f5ff95
-- title:
--   Pj: fr W add
-- statement:
--   The Pj construction uses the fr W add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompOrd.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompOrd.lean#L21-L22

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

theorem Formalism.L2.Pj.frW_add (δ : Ix Dw → ℤ) (G G' : WTZ E) : frW δ (G + G') = frW δ G + frW δ G' := by sorry
