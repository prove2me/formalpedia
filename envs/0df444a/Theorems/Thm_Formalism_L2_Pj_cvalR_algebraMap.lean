-- Prove2me | Theorems.Thm_Formalism_L2_Pj_cvalR_algebraMap
-- name    : Formalism.L2.Pj.cvalR_algebraMap
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:33.765209+00:00
-- url     : https://prove2.me/theorems/52a0cb2c-869c-46cd-b293-0d230c2a27d9
-- title:
--   Pj: cval R algebra Map
-- statement:
--   The Pj construction uses the cval R algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ReadAlg.lean#L55-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ReadAlg.lean#L55-L55

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ReadAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open MvPolynomial
variable {K : Type} [Field K]

theorem Formalism.L2.Pj.cvalR_algebraMap (σ : K →+* ℂ) (t : K) : cvalR σ (algebraMap K (CAt σ) t) = σ t := by sorry
