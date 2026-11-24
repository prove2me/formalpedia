-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FJ_span_rat_smul_mem
-- name    : Formalism.L2.Pj.FJ.span_rat_smul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:19.848145+00:00
-- url     : https://prove2.me/theorems/76bf9afc-40ab-416e-a3e8-fb3bda0bce06
-- title:
--   FJ: span rat smul mem
-- statement:
--   The FJ construction uses the span rat smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/SpanRatSmulMem.lean#L112-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/SpanRatSmulMem.lean#L112-L137

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

theorem Formalism.L2.Pj.FJ.span_rat_smul_mem {n : ℕ} (Xs : Submodule (𝓞 E) (Fin n → E)) (e : E)
    {w : Fin n → E} (hw : w ∈ Submodule.span ℚ (Xs : Set (Fin n → E))) :
    e • w ∈ Submodule.span ℚ (Xs : Set (Fin n → E)) := by sorry
