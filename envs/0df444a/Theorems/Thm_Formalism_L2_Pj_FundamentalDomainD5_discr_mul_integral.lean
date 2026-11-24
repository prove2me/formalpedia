-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_discr_mul_integral
-- name    : Formalism.L2.Pj.FundamentalDomainD5.discr_mul_integral
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:17.493349+00:00
-- url     : https://prove2.me/theorems/a43859b4-ddf1-42f1-bd7d-52556a7d11cb
-- title:
--   Fundamental Domain D5: discr mul integral
-- statement:
--   The Fundamental Domain D5 construction uses the discr mul integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/DiscrMulIntegral.lean#L11-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/DiscrMulIntegral.lean#L11-L46

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_DiscrMulIntegral
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
open NumberField Matrix

theorem Formalism.L2.Pj.FundamentalDomainD5.discr_mul_integral {K : Type} [Field K] [NumberField K] (z : K)
    (hz : ∀ a : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (z * a) = n) :
    IsIntegral ℤ ((NumberField.discr K : K) * z) := by sorry
