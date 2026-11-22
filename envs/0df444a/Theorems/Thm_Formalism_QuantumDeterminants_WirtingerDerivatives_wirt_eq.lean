-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_wirt_eq
-- name    : Formalism.QuantumDeterminants.WirtingerDerivatives.wirt_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:12:58.009023+00:00
-- url     : https://prove2.me/theorems/67c18ca8-e6d3-4233-a37f-2193b051bb78
-- title:
--   Wirtinger Derivatives: wirt eq
-- statement:
--   The Wirtinger Derivatives construction uses the wirt eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L44-L46

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

theorem Formalism.QuantumDeterminants.WirtingerDerivatives.wirt_eq (l : Fin m) (g : (Fin m → ℂ) → E) (x : Fin m → ℂ) :
    wirt l g x = Wc (Pi.single l 1) (Pi.single l Complex.I) (-Complex.I) (fderiv ℝ g x) := by sorry
