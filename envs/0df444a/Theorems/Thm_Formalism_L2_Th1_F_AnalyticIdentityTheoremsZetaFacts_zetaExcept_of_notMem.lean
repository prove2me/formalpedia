-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_AnalyticIdentityTheoremsZetaFacts_zetaExcept_of_notMem
-- name    : Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts.zetaExcept_of_notMem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:48:17.381397+00:00
-- url     : https://prove2.me/theorems/62a53da7-894b-4841-aa7e-6f456803167c
-- title:
--   Analytic Identity Theorems Zeta Facts: zeta Except of not Mem
-- statement:
--   The Analytic Identity Theorems Zeta Facts construction uses the zeta Except of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/AnalyticIdentityTheoremsZetaFacts.lean#L50-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/AnalyticIdentityTheoremsZetaFacts.lean#L50-L59

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_AnalyticIdentityTheoremsZetaFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts

theorem Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts.zetaExcept_of_notMem (L : PeriodPair) (l₀ : ℂ) (hl : l₀ ∉ L.lattice) :
    zetaExcept L l₀ = wZeta L := by sorry
