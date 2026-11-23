-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FJ_exists_smul_mem
-- name    : Formalism.L2.Pj.FJ.exists_smul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:32:41.046115+00:00
-- url     : https://prove2.me/theorems/2f82687a-f692-479e-bb78-fe6ac3300776
-- title:
--   FJ: exists smul mem
-- statement:
--   The FJ construction uses the exists smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/SpanRatSmulMem.lean#L139-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/SpanRatSmulMem.lean#L139-L140

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LocalSituation
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SpanRatSmulMem
import Theorems.Thm_UpperTheory_Reformulated_B_LocalSituation_exists_smul_mem

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

theorem Formalism.L2.Pj.FJ.exists_smul_mem (X : Data E r) (w : Fin r → E) : ∃ c : 𝓞 E, c ≠ 0 ∧ c • w ∈ X.Λ := by sorry
