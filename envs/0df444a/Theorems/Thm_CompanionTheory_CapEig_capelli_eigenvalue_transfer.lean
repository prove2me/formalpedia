-- Prove2me | Theorems.Thm_CompanionTheory_CapEig_capelli_eigenvalue_transfer
-- name    : CompanionTheory.CapEig.capelli_eigenvalue_transfer
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:56:51.625605+00:00
-- url     : https://prove2.me/theorems/d29c263b-883c-52f7-89fa-a493c2c40a1f
-- title:
--   Cap Eig: capelli eigenvalue transfer
-- statement:
--   The Cap Eig construction uses the capelli eigenvalue transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/CoefEig.lean#L48-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/CoefEig.lean#L48-L55

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_FunAct
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_CoefEig
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PI.UpqRep Formalism.FourierDecayAlt
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.CapEig

theorem CompanionTheory.CapEig.capelli_eigenvalue_transfer : CompanionTheory.LimBd.Main.CVBridge := by sorry
