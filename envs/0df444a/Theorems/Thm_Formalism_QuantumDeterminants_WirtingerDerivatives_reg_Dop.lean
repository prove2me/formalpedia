-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_reg_Dop
-- name    : Formalism.QuantumDeterminants.WirtingerDerivatives.reg_Dop
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:04:10.76802+00:00
-- url     : https://prove2.me/theorems/8b4400d2-0419-4546-884a-ee671ae85152
-- title:
--   Wirtinger Derivatives: reg Dop
-- statement:
--   The Wirtinger Derivatives construction uses the reg Dop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L286-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L286-L300

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

theorem Formalism.QuantumDeterminants.WirtingerDerivatives.reg_Dop {g : (Fin m → ℂ) → E} (hg : Reg g) (k : Fin m) (j : Fin 6) : Reg (Dop k j g) := by sorry
