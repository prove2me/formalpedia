-- Prove2me | Theorems.Thm_Formalism_SLP_GlobalBoundRefinements_P_coefficients_of_form_preserving
-- name    : Formalism.SLP.GlobalBoundRefinements.P.coefficients_of_form_preserving
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:29:34.783959+00:00
-- url     : https://prove2.me/theorems/24ea9a89-82a5-4645-a876-a396d137aaaa
-- title:
--   P: coefficients of form preserving
-- statement:
--   The P construction uses the coefficients of form preserving property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/DetIndexProductHyperbolicInequality.lean#L33-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/DetIndexProductHyperbolicInequality.lean#L33-L66

import Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_DetIndexProductHyperbolicInequality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.GlobalBoundRefinements Formalism.SLP.GlobalBoundRefinements.P
open Formalism.SLP.GlobalBoundRefinements
set_option maxHeartbeats 800000

theorem Formalism.SLP.GlobalBoundRefinements.P.coefficients_of_form_preserving : Formalism.SLP.GlobalBoundRefinements.FormCoeff := by sorry
