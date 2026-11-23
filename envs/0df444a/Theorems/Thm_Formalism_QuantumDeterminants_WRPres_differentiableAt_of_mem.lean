-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WRPres_differentiableAt_of_mem
-- name    : Formalism.QuantumDeterminants.WRPres.differentiableAt_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:40.365328+00:00
-- url     : https://prove2.me/theorems/9da8840d-0ed3-43b1-b916-e913b97dc0a2
-- title:
--   WRPres: differentiable At of mem
-- statement:
--   The WRPres construction uses the differentiable At of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRPres.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRPres.lean#L41-L44

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRPres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WRPres
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.QuantumDeterminants.WRPres.differentiableAt_of_mem {f : (Fin m → ℂ) → E} (hf : f ∈ WSm m E) {x : Fin m → ℂ}
    (hx : x ∈ OmX m) : DifferentiableAt ℝ f x := by sorry
