-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_opL_off
-- name    : Formalism.QuantumDeterminants.WirtingerDerivatives.opL_off
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:18:40.758015+00:00
-- url     : https://prove2.me/theorems/4b45d33d-cd32-4627-be4d-9356215209b9
-- title:
--   Wirtinger Derivatives: op L off
-- statement:
--   The Wirtinger Derivatives construction uses the op L off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L276-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L276-L284

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

theorem Formalism.QuantumDeterminants.WirtingerDerivatives.opL_off (k : Fin m) (j : Fin 6) (g : (Fin m → ℂ) → E) {x : Fin m → ℂ} (hx : x ∉ OmX m)
    (h0 : g x = 0) : opL k j g x = 0 := by sorry
