-- Prove2me | Theorems.Thm_Formalism_L2_Pj_nrmC_zero
-- name    : Formalism.L2.Pj.nrmC_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:44.027802+00:00
-- url     : https://prove2.me/theorems/fe3c9a98-0f83-489b-9dce-6ef664e48f06
-- title:
--   Pj: nrm C zero
-- statement:
--   The Pj construction uses the nrm C zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompOrd.lean#L80-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompOrd.lean#L80-L81

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
variable (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
  (yP : ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))

theorem Formalism.L2.Pj.nrmC_zero (G : WTZ E) (P : Om Z →+* ℂ) : nrmC fn yP G 0 P = 0 := by sorry
