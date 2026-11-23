-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_AnalyticIdentityTheoremsZetaFacts_differentiableOn_wZeta
-- name    : Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts.differentiableOn_wZeta
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:24:32.51123+00:00
-- url     : https://prove2.me/theorems/b699884f-dcc2-422b-a5e7-cc2aa69791cb
-- title:
--   Analytic Identity Theorems Zeta Facts: differentiable On w Zeta
-- statement:
--   The Analytic Identity Theorems Zeta Facts construction uses the differentiable On w Zeta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/AnalyticIdentityTheoremsZetaFacts.lean#L181-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/AnalyticIdentityTheoremsZetaFacts.lean#L181-L191

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

theorem Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts.differentiableOn_wZeta (L : PeriodPair) :
    DifferentiableOn ℂ (wZeta L) (L.lattice : Set ℂ)ᶜ := by sorry
