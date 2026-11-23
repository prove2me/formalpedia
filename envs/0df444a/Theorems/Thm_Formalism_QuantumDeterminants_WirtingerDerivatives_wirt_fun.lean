-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_wirt_fun
-- name    : Formalism.QuantumDeterminants.WirtingerDerivatives.wirt_fun
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:42:29.112591+00:00
-- url     : https://prove2.me/theorems/763b823c-d90a-461f-b3c0-e69273ffa90e
-- title:
--   Wirtinger Derivatives: wirt fun
-- statement:
--   The Wirtinger Derivatives construction uses the wirt fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L117-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L117-L120

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

theorem Formalism.QuantumDeterminants.WirtingerDerivatives.wirt_fun (l : Fin m) (g : (Fin m → ℂ) → E) :
    wirt l g = fun y => Wc (Pi.single l 1) (Pi.single l Complex.I) (-Complex.I) (fderiv ℝ g y) := by sorry
