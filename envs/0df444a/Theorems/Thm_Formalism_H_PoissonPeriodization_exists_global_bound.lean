-- Prove2me | Theorems.Thm_Formalism_H_PoissonPeriodization_exists_global_bound
-- name    : Formalism.H.PoissonPeriodization.exists_global_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:45.155377+00:00
-- url     : https://prove2.me/theorems/9d50fc34-021d-40b8-b775-4f06ef9c94f9
-- title:
--   Poisson Periodization: exists global bound
-- statement:
--   The Poisson Periodization construction uses the exists global bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/Periodization.lean#L14-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/Periodization.lean#L14-L60

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_Periodization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Asymptotics Complex Metric
open scoped RealInnerProductSpace
noncomputable section
open Formalism Formalism.H
open Formalism.H.PoissonPeriodization
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem Formalism.H.PoissonPeriodization.exists_global_bound {f : V → ℂ} (hf : Continuous f) {b : ℝ} (hb : 0 ≤ b)
    (hO : f =O[cocompact V] (fun v => ‖v‖ ^ (-b))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, ‖f v‖ ≤ C * (1 + ‖v‖) ^ (-b) := by sorry
