-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FJ_trBE_sepLeft
-- name    : Formalism.L2.Pj.FJ.trBE_sepLeft
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:26.23481+00:00
-- url     : https://prove2.me/theorems/e4eb5cc4-bea1-45fe-9261-c2f13bedd54e
-- title:
--   FJ: tr BE sep Left
-- statement:
--   The FJ construction uses the tr BE sep Left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/SpanRatSmulMem.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/SpanRatSmulMem.lean#L31-L37

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

theorem Formalism.L2.Pj.FJ.trBE_sepLeft (n : ℕ) : LinearMap.SeparatingLeft (trBE (E := E) n) := by sorry
