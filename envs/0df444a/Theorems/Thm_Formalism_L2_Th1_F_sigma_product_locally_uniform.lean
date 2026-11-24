-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_sigma_product_locally_uniform
-- name    : Formalism.L2.Th1.F.sigma_product_locally_uniform
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:56.096816+00:00
-- url     : https://prove2.me/theorems/aeead2db-9f9e-40f9-b2ac-f8f24ee5ffff
-- title:
--   F: sigma product locally uniform
-- statement:
--   The F construction uses the sigma product locally uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaConv.lean#L121-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaConv.lean#L121-L134

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaConv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open SigmaConv

theorem Formalism.L2.Th1.F.sigma_product_locally_uniform : SigmaProdLU := by sorry
