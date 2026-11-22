-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FJ_FnVia_smul_apply
-- name    : Formalism.L2.Pj.FJ.FnVia.smul_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:44:54.555221+00:00
-- url     : https://prove2.me/theorems/a0739af4-c9b0-4619-913c-74e63310eca5
-- title:
--   Fn Via: smul apply
-- statement:
--   The Fn Via construction uses the smul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IntegrableOnIntegrand.lean#L106-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IntegrableOnIntegrand.lean#L106-L107

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
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
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Pj
open Formalism.L2.Pj.FJ
variable {K : Type} [Field K]
variable (σ : K →+* ℂ) (Ω : Type)
variable {σ Ω}

theorem Formalism.L2.Pj.FJ.FnVia.smul_apply (a : K) (f : FnVia σ Ω) (x : Ω) :
    (show Ω → ℂ from a • f) x = σ a * (show Ω → ℂ from f) x := by sorry
