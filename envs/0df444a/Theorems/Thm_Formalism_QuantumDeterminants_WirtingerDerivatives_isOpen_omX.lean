-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_isOpen_omX
-- name    : Formalism.QuantumDeterminants.WirtingerDerivatives.isOpen_omX
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:10:50.194096+00:00
-- url     : https://prove2.me/theorems/c021e475-9172-4225-b7b0-1c4153453d4a
-- title:
--   Wirtinger Derivatives: is Open om X
-- statement:
--   The Wirtinger Derivatives construction uses the is Open om X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L14-L17

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

theorem Formalism.QuantumDeterminants.WirtingerDerivatives.isOpen_omX (m : ℕ) : IsOpen (OmX m) := by sorry
