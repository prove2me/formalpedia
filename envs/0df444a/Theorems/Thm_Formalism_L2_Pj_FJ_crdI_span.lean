-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FJ_crdI_span
-- name    : Formalism.L2.Pj.FJ.crdI_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:14.70086+00:00
-- url     : https://prove2.me/theorems/6cee15c4-85f7-4e92-9563-f3a939542c0f
-- title:
--   FJ: crd I span
-- statement:
--   The FJ construction uses the crd I span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/SpanRatSmulMem.lean#L142-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/SpanRatSmulMem.lean#L142-L174

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

theorem Formalism.L2.Pj.FJ.crdI_span (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (h𝔄 : 𝔄 ≠ 0) {X : Data E r}
    (cu : CuspFD X ρ) : Submodule.span ℚ (crdI 𝔄 cu : Set (Fin ρ → E)) = ⊤ := by sorry
