-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_Dop_comm
-- name    : Formalism.QuantumDeterminants.WirtingerDerivatives.Dop_comm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:18:31.168608+00:00
-- url     : https://prove2.me/theorems/b38caf95-e341-4663-8d33-6cfc3370d6e1
-- title:
--   Wirtinger Derivatives: Dop comm
-- statement:
--   The Wirtinger Derivatives construction uses the Dop comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L340-L374
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L340-L374

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

theorem Formalism.QuantumDeterminants.WirtingerDerivatives.Dop_comm {g : (Fin m → ℂ) → E} (hg : Reg g) {x : Fin m → ℂ} (hx : x ∈ OmX m)
    (l k : Fin m) (i j : Fin 6) : Dop l i (Dop k j g) x = Dop k j (Dop l i g) x := by sorry
