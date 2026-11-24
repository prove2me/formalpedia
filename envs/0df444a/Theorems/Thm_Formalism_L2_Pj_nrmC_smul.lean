-- Prove2me | Theorems.Thm_Formalism_L2_Pj_nrmC_smul
-- name    : Formalism.L2.Pj.nrmC_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:18.713592+00:00
-- url     : https://prove2.me/theorems/2f76d0a9-b784-4e0f-8ec2-1dbbcbc4c1ad
-- title:
--   Pj: nrm C smul
-- statement:
--   The Pj construction uses the nrm C smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompOrd.lean#L107-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompOrd.lean#L107-L110

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

theorem Formalism.L2.Pj.nrmC_smul {G : WTZ E} {f : AC Z} (P : Om Z →+* ℂ) (a : Om Z) (hf : f ∈ AG Z G) :
    nrmC fn yP G (a • f) P = ‖P a‖ * nrmC fn yP G f P := by sorry
