-- Prove2me | Theorems.Thm_Formalism_L2_Pj_nrmC_mul
-- name    : Formalism.L2.Pj.nrmC_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:28.694804+00:00
-- url     : https://prove2.me/theorems/43b76b0c-41c7-471e-805f-e2f411433c12
-- title:
--   Pj: nrm C mul
-- statement:
--   The Pj construction uses the nrm C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompOrd.lean#L95-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompOrd.lean#L95-L105

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

theorem Formalism.L2.Pj.nrmC_mul (hfn : FnNe Xo c fn) {G G' : WTZ E} {f g : AC Z} (P : Om Z →+* ℂ) (hf : f ∈ AG Z G)
    (hg : g ∈ AG Z G') : nrmC fn yP (G + G') (f * g) P = nrmC fn yP G f P * nrmC fn yP G' g P := by sorry
