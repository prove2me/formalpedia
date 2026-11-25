-- Prove2me | Theorems.Thm_Formalism_L2_Pj_algebraMap_CAt
-- name    : Formalism.L2.Pj.algebraMap_CAt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:45:59.546534+00:00
-- url     : https://prove2.me/theorems/844dfa74-043c-5a17-b1e4-1912e62f037e
-- title:
--   Pj: algebra Map CAt
-- statement:
--   The Pj construction uses the algebra Map CAt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AlgebraMapCAt.lean#L102-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AlgebraMapCAt.lean#L102-L102

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
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

theorem Formalism.L2.Pj.algebraMap_CAt (σ : K →+* ℂ) (c : K) : (show ℂ from algebraMap K (CAt σ) c) = σ c := by sorry
