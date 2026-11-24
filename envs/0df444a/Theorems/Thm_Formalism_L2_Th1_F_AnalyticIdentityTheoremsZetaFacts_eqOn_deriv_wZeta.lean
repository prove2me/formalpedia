-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_AnalyticIdentityTheoremsZetaFacts_eqOn_deriv_wZeta
-- name    : Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts.eqOn_deriv_wZeta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:17.46189+00:00
-- url     : https://prove2.me/theorems/d1ef2f17-907b-43a2-a260-47e636285135
-- title:
--   Analytic Identity Theorems Zeta Facts: eq On deriv w Zeta
-- statement:
--   The Analytic Identity Theorems Zeta Facts construction uses the eq On deriv w Zeta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/AnalyticIdentityTheoremsZetaFacts.lean#L154-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/AnalyticIdentityTheoremsZetaFacts.lean#L154-L179

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

theorem Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts.eqOn_deriv_wZeta (L : PeriodPair) :
    Set.EqOn (deriv (wZeta L)) (fun z ↦ -(L.weierstrassP z)) (L.lattice : Set ℂ)ᶜ := by sorry
