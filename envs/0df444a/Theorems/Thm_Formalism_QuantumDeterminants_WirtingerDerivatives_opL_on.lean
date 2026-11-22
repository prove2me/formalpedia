-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_opL_on
-- name    : Formalism.QuantumDeterminants.WirtingerDerivatives.opL_on
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:08:35.473802+00:00
-- url     : https://prove2.me/theorems/f9f9ad54-be3b-4b38-95cd-8684c72aa018
-- title:
--   Wirtinger Derivatives: op L on
-- statement:
--   The Wirtinger Derivatives construction uses the op L on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L272-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L272-L274

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

theorem Formalism.QuantumDeterminants.WirtingerDerivatives.opL_on (k : Fin m) (j : Fin 6) (g : (Fin m → ℂ) → E) {x : Fin m → ℂ} (hx : x ∈ OmX m) :
    opL k j g x = coef k j x • Dop k j g x := by sorry
