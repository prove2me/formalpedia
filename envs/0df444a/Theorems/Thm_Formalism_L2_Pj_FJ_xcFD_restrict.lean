-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FJ_xcFD_restrict
-- name    : Formalism.L2.Pj.FJ.xcFD_restrict
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:40.130828+00:00
-- url     : https://prove2.me/theorems/f393d838-6bf7-4e3a-a809-c0d2274aa53d
-- title:
--   FJ: xc FD restrict
-- statement:
--   The FJ construction uses the xc FD restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/SpanRatSmulMem.lean#L192-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/SpanRatSmulMem.lean#L192-L195

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

theorem Formalism.L2.Pj.FJ.xcFD_restrict (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) {X : Data E r} (cu : CuspFD X ρ) :
    (XcFD 𝔄 cu).restrictScalars ℤ = (trBE ρ).dualSubmodule ((crdI 𝔄 cu).restrictScalars ℤ) := by sorry
