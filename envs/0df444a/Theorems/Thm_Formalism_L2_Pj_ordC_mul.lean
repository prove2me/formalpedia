-- Prove2me | Theorems.Thm_Formalism_L2_Pj_ordC_mul
-- name    : Formalism.L2.Pj.ordC_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:24.799314+00:00
-- url     : https://prove2.me/theorems/4fb18338-11f5-417c-94cd-765174218cf5
-- title:
--   Pj: ord C mul
-- statement:
--   The Pj construction uses the ord C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompOrd.lean#L36-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompOrd.lean#L36-L49

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
variable {Z : Comp Xo c}

theorem Formalism.L2.Pj.ordC_mul (δ : Ix Dw → ℤ) (v : AddValuation (Om Z) (WithTop ℤ)) {G G' : WTZ E} {f g : AC Z}
    (hf : f ∈ AG Z G) (hg : g ∈ AG Z G') (hf0 : f ≠ 0) (hg0 : g ≠ 0) :
    ordC δ v (G + G') (f * g) = ordC δ v G f + ordC δ v G' g := by sorry
