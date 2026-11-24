-- Prove2me | Theorems.Thm_Formalism_SLP_GlobalBoundRefinements_P_entry_MNinv
-- name    : Formalism.SLP.GlobalBoundRefinements.P.entry_MNinv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:29:35.426798+00:00
-- url     : https://prove2.me/theorems/e855563c-75ae-40db-97e1-d4899d31ab14
-- title:
--   P: entry MNinv
-- statement:
--   The P construction uses the entry MNinv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/TheoremBEntryFormula.lean#L66-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/TheoremBEntryFormula.lean#L66-L74

import Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_ArithmeticLatticeHypothesis
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_TheoremBEntryFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SLP Formalism.SLP.GlobalBoundRefinements Formalism.SLP.GlobalBoundRefinements.P
open Formalism.SLP.GlobalBoundRefinements

theorem Formalism.SLP.GlobalBoundRefinements.P.entry_MNinv (M N : Matrix (Fin 2) (Fin 2) ℂ) (h : N.conjTranspose * J * N = J) :
    (M * N⁻¹) 1 0 = M 1 0 * (starRingEnd ℂ) (N 0 0) - M 1 1 * (starRingEnd ℂ) (N 0 1) := by sorry
