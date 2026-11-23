-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_isogenyWeierstrassP_of_ellipticNoPole
-- name    : Formalism.L2.Th1.F.isogenyWeierstrassP_of_ellipticNoPole
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:27:42.205529+00:00
-- url     : https://prove2.me/theorems/1f05f8b0-df75-4cae-8c80-6f635b47e464
-- title:
--   F: isogeny Weierstrass P of elliptic No Pole
-- statement:
--   The F construction uses the isogeny Weierstrass P of elliptic No Pole property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IsogenyP.lean#L74-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IsogenyP.lean#L74-L151

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Elliptic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenyP
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
open IsogenyPAux

theorem Formalism.L2.Th1.F.isogenyWeierstrassP_of_ellipticNoPole (hN : EllipticNoPole) : IsogenyP := by sorry
