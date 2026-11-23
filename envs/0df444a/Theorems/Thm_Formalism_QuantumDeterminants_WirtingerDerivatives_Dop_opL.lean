-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_Dop_opL
-- name    : Formalism.QuantumDeterminants.WirtingerDerivatives.Dop_opL
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:04:02.618976+00:00
-- url     : https://prove2.me/theorems/21a4c34d-1aa9-4f9e-afc1-fe592523e26a
-- title:
--   Wirtinger Derivatives: Dop op L
-- statement:
--   The Wirtinger Derivatives construction uses the Dop op L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L312-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L312-L338

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

theorem Formalism.QuantumDeterminants.WirtingerDerivatives.Dop_opL {g : (Fin m → ℂ) → E} (hg : Reg g) {x : Fin m → ℂ} (hx : x ∈ OmX m)
    (l k : Fin m) (i j : Fin 6) :
    Dop l i (opL k j g) x = dco l i k j x • Dop k j g x + coef k j x • Dop l i (Dop k j g) x := by sorry
