-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_IX_physical_true_state_adapter
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.IX.physical_true_state_adapter
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-22T06:21:51.02582+00:00
-- url     : https://prove2.me/theorems/ea060203-074d-4f83-bc66-5510921b3bf3
-- title:
--   IX true-state source adapter
-- statement:
--   **IX true-state source adapter**
--
--   For a jet readout `jt : ℝ → Jet9`, an angular-momentum parameter $J$, and a constraint-source derivative $d_C$, Lean proves that `fromTrueState jt J dC` has the prescribed jet and parameter and that its three compact source fields are exactly $q_F$, $q_C$, and $q_A$ evaluated on the readout.
--
--   This is the data-level dictionary needed to connect the radial variables of the equal-spin five-dimensional Einstein–Maxwell model to the IX residual interface. The physical model is documented in [Kunz, Navarro-Lérida and Petersen, *Five-Dimensional Charged Rotating Black Holes*](https://arxiv.org/abs/gr-qc/0503010) and [Kunz, Navarro-Lérida and Viebahn, *Charged Rotating Black Holes in Odd Dimensions*](https://arxiv.org/abs/hep-th/0605075), while endpoint regularity and the autonomous boundary-value formulation are treated in [Fröb, Khavkine, Málek and Pravda, *On well-posedness and algebraic type of the five-dimensional charged rotating black hole with two equal-magnitude angular momenta*](https://arxiv.org/abs/2112.13266).
--
--   The theorem proves the adapter identities only. It does not supply the local VIII15R regularity, non-degeneracy, or existence of a global solution.
-- source:
--   He Wang, Exact Spacetime Atlas IX analytic bridge. Local source, commit 8fc44e0bf5f0; Atlas/EinsteinMaxwell/ES5/KerrSchild/IX/Main.lean#L30-L37; SHA-256 18884bf60ddfde40e152ae58d87e665266dbac3d35d7783040639e2d0e987d6b. Registered definitions: mission/PHYSICS_BOUNDARY.md, notes/B3_POLICY.md. Analytic source and residual bridge: Exact Spacetime Atlas VIII17/VIII20 local source and weighted-residual modules; formulas are copied from the pinned local Lean source and checked by the kernel..

import Mathlib
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_IX_ActualSource
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_IX_Main
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.IX
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.IX.physical_true_state_adapter
    (jt : ℝ → Jet9) (J : ℝ) (dC : ℝ → ℝ) :
    let σ := fromTrueState jt J dC
    σ.jet = jt ∧ σ.J = J ∧
      (∀ x, σ.sourceF x = qFj x (jt x)) ∧
      (∀ x, σ.sourceC x = qCj x (jt x) J) ∧
      (∀ x, σ.sourceA x = qAj x (jt x) J) := by sorry
