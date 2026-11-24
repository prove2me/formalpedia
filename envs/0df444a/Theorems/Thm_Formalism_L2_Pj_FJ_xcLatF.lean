-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FJ_xcLatF
-- name    : Formalism.L2.Pj.FJ.xcLatF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:41.154527+00:00
-- url     : https://prove2.me/theorems/80ee0148-f1ad-4725-8733-6b0391791f6d
-- title:
--   FJ: xc Lat F
-- statement:
--   The FJ construction uses the xc Lat F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/SpanRatSmulMem.lean#L222-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/SpanRatSmulMem.lean#L222-L224

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LocalSituation
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SpanRatSmulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FJ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem Formalism.L2.Pj.FJ.xcLatF {Comp : Type} (X : Comp → Data E r) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (h𝔄 : 𝔄 ≠ 0) : XcLatF X 𝔄 ρ := by sorry
