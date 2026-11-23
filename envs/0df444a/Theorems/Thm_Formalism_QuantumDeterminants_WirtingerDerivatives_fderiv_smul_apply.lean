-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_fderiv_smul_apply
-- name    : Formalism.QuantumDeterminants.WirtingerDerivatives.fderiv_smul_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:37.610274+00:00
-- url     : https://prove2.me/theorems/7f14f416-791a-4813-8bca-af6aaf2649dd
-- title:
--   Wirtinger Derivatives: fderiv smul apply
-- statement:
--   The Wirtinger Derivatives construction uses the fderiv smul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L99-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L99-L107

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

theorem Formalism.QuantumDeterminants.WirtingerDerivatives.fderiv_smul_apply {a : (Fin m → ℂ) → ℂ} {h : (Fin m → ℂ) → E} {x : Fin m → ℂ}
    (ha : DifferentiableAt ℝ a x) (hh : DifferentiableAt ℝ h x) (v : Fin m → ℂ) :
    fderiv ℝ (fun y => a y • h y) x v = a x • fderiv ℝ h x v + fderiv ℝ a x v • h x := by sorry
