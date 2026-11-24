-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FJ_integrableOn_integrand
-- name    : Formalism.L2.Pj.FJ.integrableOn_integrand
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:14.929217+00:00
-- url     : https://prove2.me/theorems/2dd966ae-743c-4b17-b6d3-7dddbecde91d
-- title:
--   FJ: integrable On integrand
-- statement:
--   The FJ construction uses the integrable On integrand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IntegrableOnIntegrand.lean#L81-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IntegrableOnIntegrand.lean#L81-L88

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
variable {Ω : Type} {N : ℕ}

theorem Formalism.L2.Pj.FJ.integrableOn_integrand [TopologicalSpace Ω] {act : (Fin N → ℝ) → Ω → Ω} {ph : Fin N → ℝ}
    {P : Ω → ℂ} {x : Ω} {T : Set Ω} (hP : ContinuousOn P T) (hact : Continuous fun t => act t x)
    (hT : ∀ t ∈ cube N, act t x ∈ T) : IntegrableOn (integrand act ph P x) (cube N) := by sorry
