-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_reg_opL
-- name    : Formalism.QuantumDeterminants.WirtingerDerivatives.reg_opL
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:51:44.326558+00:00
-- url     : https://prove2.me/theorems/25d8e06b-dd1a-43e9-8f39-8086d1cd1e38
-- title:
--   Wirtinger Derivatives: reg op L
-- statement:
--   The Wirtinger Derivatives construction uses the reg op L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L302-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L302-L304

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

theorem Formalism.QuantumDeterminants.WirtingerDerivatives.reg_opL {g : (Fin m → ℂ) → E} (hg : Reg g) (k : Fin m) (j : Fin 6) : Reg (opL k j g) := by sorry
