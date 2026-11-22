-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_opL_ev
-- name    : Formalism.QuantumDeterminants.WirtingerDerivatives.opL_ev
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:08:18.837805+00:00
-- url     : https://prove2.me/theorems/4048a841-4a34-4a0d-8a7a-3ef13afae9e6
-- title:
--   Wirtinger Derivatives: op L ev
-- statement:
--   The Wirtinger Derivatives construction uses the op L ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L255-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L255-L270

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open Filter
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WirtingerDerivatives
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.QuantumDeterminants.WirtingerDerivatives.opL_ev (k : Fin m) (j : Fin 6) (g : (Fin m → ℂ) → E) {x : Fin m → ℂ} (hx : x ∈ OmX m) :
    opL k j g =ᶠ[𝓝 x] fun y => coef k j y • Dop k j g y := by sorry
