-- Prove2me | Theorems.Thm_CompanionTheory_CapEig_coefEig_of_infChar
-- name    : CompanionTheory.CapEig.coefEig_of_infChar
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:56:12.522897+00:00
-- url     : https://prove2.me/theorems/bc7e1e63-d78c-535d-9ddf-541be82a7a58
-- title:
--   Cap Eig: coef Eig of inf Char
-- statement:
--   The Cap Eig construction uses the coef Eig of inf Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/CoefEigOfInfChar.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/CoefEigOfInfChar.lean#L6-L7

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_CoefEig
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_AdmissibleOfIwasawa
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_CoefEigOfInfChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.CapEig

theorem CompanionTheory.CapEig.coefEig_of_infChar (hI : PI.DSInfCharCap.DSInfCharCap) : CompanionTheory.LimBd.Main.CoefEig := by sorry
