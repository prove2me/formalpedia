-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_reg_of_mem
-- name    : Formalism.QuantumDeterminants.WirtingerDerivatives.reg_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:58.829925+00:00
-- url     : https://prove2.me/theorems/acbd299e-ab0e-480a-a1f7-816bd84670e3
-- title:
--   Wirtinger Derivatives: reg of mem
-- statement:
--   The Wirtinger Derivatives construction uses the reg of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L67-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L67-L69

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

theorem Formalism.QuantumDeterminants.WirtingerDerivatives.reg_of_mem {f : (Fin m → ℂ) → E} (hf : f ∈ WSm m E) : Reg f := by sorry
