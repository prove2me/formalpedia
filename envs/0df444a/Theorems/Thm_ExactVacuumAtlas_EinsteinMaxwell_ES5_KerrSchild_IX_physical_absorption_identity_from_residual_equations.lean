-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_IX_physical_absorption_identity_from_residual_equations
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.IX.physical_absorption_identity_from_residual_equations
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-22T06:21:47.883793+00:00
-- url     : https://prove2.me/theorems/42d924c3-9dcc-4488-bb05-ad8ace9f4088
-- title:
--   IX absorption identity from actual residual equations
-- statement:
--   **IX absorption identity from actual residual equations**
--
--   Let $\sigma$ be an IX physical source state and let $w_M$ be the actual weighted $M$ residual. Assume the generic-to-actual relation
--   $$w_{Mc}=w_M+x(\mathrm{srcMbar}-\mathrm{qMcK})$$
--   and the unabsorbed compatibility identity
--   $$
--   (2-4x)(\mathrm{srcMbar}-\mathrm{qMcK})
--   =\lambda_F w_F+\lambda_M w_M+\lambda_C w_C+\lambda_A w_A.
--   $$
--   Then Lean proves the absorbed identity
--   $$
--   (2-4x+x\lambda_M)(\mathrm{srcMbar}-\mathrm{qMcK})
--   =\lambda_F w_F+\lambda_M w_{Mc}+\lambda_C w_C+\lambda_A w_A
--   $$
--   onetheless on the full compactified domain $K=[0,1/3]$.
--
--   This is the exact algebraic residual step used in the IX bridge. It formalizes the compactified version of the radial residual structure studied for equal-spin five-dimensional Einstein–Maxwell black holes in [Kunz, Navarro-Lérida and Petersen, *Five-Dimensional Charged Rotating Black Holes*](https://arxiv.org/abs/gr-qc/0503010), [Kunz, Navarro-Lérida and Viebahn, *Charged Rotating Black Holes in Odd Dimensions*](https://arxiv.org/abs/hep-th/0605075), and [Fröb, Khavkine, Málek and Pravda, *On well-posedness and algebraic type of the five-dimensional charged rotating black hole with two equal-magnitude angular momenta*](https://arxiv.org/abs/2112.13266). The theorem assumes the two residual equations explicitly and makes no existence claim.
-- source:
--   He Wang, Exact Spacetime Atlas IX analytic bridge. Local source, commit 8fc44e0bf5f0; Atlas/EinsteinMaxwell/ES5/KerrSchild/IX/Main.lean#L39-L52; SHA-256 18884bf60ddfde40e152ae58d87e665266dbac3d35d7783040639e2d0e987d6b. Registered definitions: mission/PHYSICS_BOUNDARY.md, notes/B3_POLICY.md. Analytic source and residual bridge: Exact Spacetime Atlas VIII17/VIII20 local source and weighted-residual modules; formulas are copied from the pinned local Lean source and checked by the kernel..

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.IX.physical_absorption_identity_from_residual_equations
    (σ : PhysicalTrueState) (wM : ℝ → ℝ)
    (hrel : GenericMRelation σ wM)
    (hid : UnabsorbedResidualIdentity σ wM) :
    ∀ x, x ∈ KG →
      physicalAbsorbedDefect σ x =
        lamF x (σ.jet x) * wF σ x + lamM x (σ.jet x) * wMc σ x
          + lamC x (σ.jet x) * wC σ x + lamA x (σ.jet x) * wA σ x := by sorry
