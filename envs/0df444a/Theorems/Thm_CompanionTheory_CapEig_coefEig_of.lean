-- Prove2me | Theorems.Thm_CompanionTheory_CapEig_coefEig_of
-- name    : CompanionTheory.CapEig.coefEig_of
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:41:43.251967+00:00
-- url     : https://prove2.me/theorems/45aca5be-5186-5b16-a879-f278bd772166
-- title:
--   Cap Eig: coef Eig of
-- statement:
--   The Cap Eig construction uses the coef Eig of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/CoefEig.lean#L57-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/CoefEig.lean#L57-L62

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

theorem CompanionTheory.CapEig.coefEig_of (hI : PI.DSInfCharCap.DSInfCharCap) (hK : PI.KFinSmooth) : CompanionTheory.LimBd.Main.CoefEig := by sorry
