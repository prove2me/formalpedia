-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenericSectionMinimum_kill_adjoin
-- name    : Formalism.L2.Pj.GenericSectionMinimum.kill_adjoin
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:36:45.490556+00:00
-- url     : https://prove2.me/theorems/a8875257-491b-4ef5-b849-216083ce3005
-- title:
--   Generic Section Minimum: kill adjoin
-- statement:
--   The Generic Section Minimum construction uses the kill adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/TotalDegreePderivLt.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/TotalDegreePderivLt.lean#L37-L43

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PowMapMemOfPowMulMem
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DerAeval
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_TotalDegreePderivLt
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
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenericSectionMinimum
open IsLocalRing Cardinal
variable {F : Type} [Field F]

theorem Formalism.L2.Pj.GenericSectionMinimum.kill_adjoin (K : Type) [Field K] [Algebra K F] {δ : F → F} (h : IsDer δ)
    (hK : ∀ c, δ (algebraMap K F c) = 0) (s : Set F) (hs : ∀ x ∈ s, δ x = 0) :
    ∀ x ∈ IntermediateField.adjoin K s, δ x = 0 := by sorry
