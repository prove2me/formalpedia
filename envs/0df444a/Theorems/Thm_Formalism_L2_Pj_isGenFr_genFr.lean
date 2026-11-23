-- Prove2me | Theorems.Thm_Formalism_L2_Pj_isGenFr_genFr
-- name    : Formalism.L2.Pj.isGenFr_genFr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:00.338884+00:00
-- url     : https://prove2.me/theorems/13add703-de95-403d-afc1-42ad42291886
-- title:
--   Pj: is Gen Fr gen Fr
-- statement:
--   The Pj construction uses the is Gen Fr gen Fr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IsGenFrGenFr.lean#L51-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IsGenFrGenFr.lean#L51-L51

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
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
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)
variable {Xo c}

theorem Formalism.L2.Pj.isGenFr_genFr (h : GenFrEx Xo c) (Z : Comp Xo c) : IsGenFr Z (genFr h Z) := by sorry
