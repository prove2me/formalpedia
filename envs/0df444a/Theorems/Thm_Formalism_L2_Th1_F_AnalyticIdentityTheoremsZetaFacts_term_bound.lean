-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_AnalyticIdentityTheoremsZetaFacts_term_bound
-- name    : Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts.term_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:24:38.764914+00:00
-- url     : https://prove2.me/theorems/7789590d-a8a1-4a82-ac41-01d63c32608f
-- title:
--   Analytic Identity Theorems Zeta Facts: term bound
-- statement:
--   The Analytic Identity Theorems Zeta Facts construction uses the term bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/AnalyticIdentityTheoremsZetaFacts.lean#L9-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/AnalyticIdentityTheoremsZetaFacts.lean#L9-L30

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

theorem Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts.term_bound (r : ℝ) (hr : 0 < r) (s : ℂ) (hs : ‖s‖ < r) (l : ℂ) (h : 2 * r ≤ ‖l‖) :
    ‖1 / (s - l) + 1 / l + s / l ^ 2‖ ≤ 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ) := by sorry
