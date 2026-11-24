-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FJ_dualZE_eq
-- name    : Formalism.L2.Pj.FJ.dualZE_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:46.468907+00:00
-- url     : https://prove2.me/theorems/dbcbc11d-fa0f-49e7-89ec-504ed34a91db
-- title:
--   FJ: dual ZE eq
-- statement:
--   The FJ construction uses the dual ZE eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/SpanRatSmulMem.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/SpanRatSmulMem.lean#L42-L47

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

theorem Formalism.L2.Pj.FJ.dualZE_eq {n : ℕ} (Xs : Submodule (𝓞 E) (Fin n → E)) :
    dualZE Xs = ((trBE n).dualSubmodule (Xs.restrictScalars ℤ) : Set (Fin n → E)) := by sorry
