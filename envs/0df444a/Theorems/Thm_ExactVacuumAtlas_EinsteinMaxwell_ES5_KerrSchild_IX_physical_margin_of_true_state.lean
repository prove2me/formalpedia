-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_IX_physical_margin_of_true_state
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.IX.physical_margin_of_true_state
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-22T06:21:51.097797+00:00
-- url     : https://prove2.me/theorems/3def3062-81da-4e51-a017-ec5529cdb02d
-- title:
--   IX physical coefficient margin
-- statement:
--   **IX physical coefficient margin**
--
--   On $K=[0,1/3]$, assume the physical coefficient estimate
--   $$|\lambda_M(x)|\leq 5/8.$$
--   Lean proves the uniform lower bound
--   $$
--   rac{11}{24}\leq 2-4x+x\lambda_M(x).
--   $$
--   The estimate supplies the positive denominator needed for the source-defect absorption step and yields the quantitative constant $24/11$ in the corresponding defect estimate.
--
--   The coefficient is the compactified residual coefficient for the equal-spin five-dimensional Einstein–Maxwell radial system. The model background is given by [Kunz, Navarro-Lérida and Petersen, *Five-Dimensional Charged Rotating Black Holes*](https://arxiv.org/abs/gr-qc/0503010) and [Kunz, Navarro-Lérida and Viebahn, *Charged Rotating Black Holes in Odd Dimensions*](https://arxiv.org/abs/hep-th/0605075); the endpoint-regular autonomous ODE formulation is given by [Fröb, Khavkine, Málek and Pravda, *On well-posedness and algebraic type of the five-dimensional charged rotating black hole with two equal-magnitude angular momenta*](https://arxiv.org/abs/2112.13266). This theorem formalizes the coefficient calculation under its explicit bound and does not assert that the bound follows from an unlinked physical solution.
-- source:
--   He Wang, Exact Spacetime Atlas IX analytic bridge. Local source, commit 8fc44e0bf5f0; Atlas/EinsteinMaxwell/ES5/KerrSchild/IX/Main.lean#L54-L66; SHA-256 18884bf60ddfde40e152ae58d87e665266dbac3d35d7783040639e2d0e987d6b. Registered definitions: mission/PHYSICS_BOUNDARY.md, notes/B3_POLICY.md. Analytic source and residual bridge: Exact Spacetime Atlas VIII17/VIII20 local source and weighted-residual modules; formulas are copied from the pinned local Lean source and checked by the kernel..

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.IX.physical_margin_of_true_state
    (σ : PhysicalTrueState)
    (hbound : ∀ x, x ∈ KG → |lamM x (σ.jet x)| ≤ (5 / 8 : ℝ)) :
    ∀ x, x ∈ KG → (11 / 24 : ℝ) ≤ absorptionCoefficient σ x := by sorry
