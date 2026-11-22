-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_wirtBar_eq
-- name    : Formalism.QuantumDeterminants.WirtingerDerivatives.wirtBar_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:12:49.885863+00:00
-- url     : https://prove2.me/theorems/f56d1f0b-2e95-4413-b0b4-cd1098f258ae
-- title:
--   Wirtinger Derivatives: wirt Bar eq
-- statement:
--   The Wirtinger Derivatives construction uses the wirt Bar eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L48-L50

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

theorem Formalism.QuantumDeterminants.WirtingerDerivatives.wirtBar_eq (l : Fin m) (g : (Fin m → ℂ) → E) (x : Fin m → ℂ) :
    wirtBar l g x = Wc (Pi.single l 1) (Pi.single l Complex.I) Complex.I (fderiv ℝ g x) := by sorry
