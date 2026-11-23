-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_AnalyticIdentityTheoremsZetaFacts_hasDerivAt_term
-- name    : Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts.hasDerivAt_term
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:24:33.44981+00:00
-- url     : https://prove2.me/theorems/69ae309b-ae3b-4b04-9890-688e114f5cae
-- title:
--   Analytic Identity Theorems Zeta Facts: has Deriv At term
-- statement:
--   The Analytic Identity Theorems Zeta Facts construction uses the has Deriv At term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/AnalyticIdentityTheoremsZetaFacts.lean#L133-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/AnalyticIdentityTheoremsZetaFacts.lean#L133-L136

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

theorem Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts.hasDerivAt_term (l z : ℂ) (h : z - l ≠ 0) :
    HasDerivAt (fun z : ℂ ↦ 1 / (z - l) + 1 / l + z / l ^ 2)
      (-(1 / (z - l) ^ 2 - 1 / l ^ 2)) z := by sorry
