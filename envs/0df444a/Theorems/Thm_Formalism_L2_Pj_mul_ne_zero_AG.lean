-- Prove2me | Theorems.Thm_Formalism_L2_Pj_mul_ne_zero_AG
-- name    : Formalism.L2.Pj.mul_ne_zero_AG
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:07.087526+00:00
-- url     : https://prove2.me/theorems/0db02d08-1e6e-4760-b4f3-fcda132dca87
-- title:
--   Pj: mul ne zero AG
-- statement:
--   The Pj construction uses the mul ne zero AG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompData.lean#L52-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompData.lean#L52-L63

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompData
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

theorem Formalism.L2.Pj.mul_ne_zero_AG {Z : Comp Xo c} {G G' : WTZ E} {f g : AC Z} (hf : f ∈ AG Z G) (hg : g ∈ AG Z G')
    (hf0 : f ≠ 0) (hg0 : g ≠ 0) : f * g ≠ 0 := by sorry
