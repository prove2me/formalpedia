-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_Wc_smul
-- name    : Formalism.QuantumDeterminants.WirtingerDerivatives.Wc_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:08:35.427816+00:00
-- url     : https://prove2.me/theorems/c4238b7e-6c0e-4fc3-9b1e-4742f87a3f88
-- title:
--   Wirtinger Derivatives: Wc smul
-- statement:
--   The Wirtinger Derivatives construction uses the Wc smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L109-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L109-L115

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

theorem Formalism.QuantumDeterminants.WirtingerDerivatives.Wc_smul {a : (Fin m → ℂ) → ℂ} {h : (Fin m → ℂ) → E} {x : Fin m → ℂ}
    (ha : DifferentiableAt ℝ a x) (hh : DifferentiableAt ℝ h x) (u w : Fin m → ℂ) (s : ℂ) :
    Wc u w s (fderiv ℝ (fun y => a y • h y) x) =
      Wc u w s (fderiv ℝ a x) • h x + a x • Wc u w s (fderiv ℝ h x) := by sorry
