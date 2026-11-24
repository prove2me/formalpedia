-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_dot_self_eq_sq_norm
-- name    : Formalism.L2.Pj.FundamentalDomainD5.dot_self_eq_sq_norm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:36.361824+00:00
-- url     : https://prove2.me/theorems/d1434b1a-678e-44e7-90bb-9f18c5b830ad
-- title:
--   Fundamental Domain D5: dot self eq sq norm
-- statement:
--   The Fundamental Domain D5 construction uses the dot self eq sq norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/DotSelfEqSqNorm.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/DotSelfEqSqNorm.lean#L11-L14

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_DotSelfEqSqNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FundamentalDomainD5
open Matrix

theorem Formalism.L2.Pj.FundamentalDomainD5.dot_self_eq_sq_norm {N : ℕ} (v : Fin N → ℝ) :
    v ⬝ᵥ v = ‖(WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm v‖ ^ 2 := by sorry
