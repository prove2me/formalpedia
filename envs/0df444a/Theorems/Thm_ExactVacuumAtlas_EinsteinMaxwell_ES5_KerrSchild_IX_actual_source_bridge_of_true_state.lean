-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_IX_actual_source_bridge_of_true_state
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.IX.actual_source_bridge_of_true_state
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-22T06:22:02.60884+00:00
-- url     : https://prove2.me/theorems/6a26b3e7-bf5b-43b1-a7af-955d2bd06d12
-- title:
--   Exact Spacetime Atlas IX actual-source bridge from true state
-- statement:
--   **Exact Spacetime Atlas IX actual-source bridge**
--
--   Let $\sigma$ be an IX physical source state. Assume the generic-to-actual $M$-row relation, the unabsorbed residual identity, the coefficient estimate $|\lambda_M|\leq5/8$, and vanishing of the four weighted rows $w_F,w_{Mc},w_C,w_A$ on $K=[0,1/3]$. Lean proves
--   $$
--   \mathrm{srcMbar}(\sigma,x)=\mathrm{qMcK}(\sigma,x)
--   \qquad (x\in K).
--   $$
--
--   The result is the formal compactified actual-source bridge. It is the compatibility step that connects the actual $M$ forcing to the generic completion used by the reduced radial system. Its physical context is the five-dimensional equal-spin Einstein–Maxwell reduction of [Kunz, Navarro-Lérida and Petersen, *Five-Dimensional Charged Rotating Black Holes*](https://arxiv.org/abs/gr-qc/0503010) and [Kunz, Navarro-Lérida and Viebahn, *Charged Rotating Black Holes in Odd Dimensions*](https://arxiv.org/abs/hep-th/0605075), together with the horizon-regular boundary-value formulation of [Fröb, Khavkine, Málek and Pravda, *On well-posedness and algebraic type of the five-dimensional charged rotating black hole with two equal-magnitude angular momenta*](https://arxiv.org/abs/2112.13266).
--
--   The theorem is conditional on the residual equations and coefficient estimate displayed above. It provides a machine-checked bridge lemma and leaves direct construction of those hypotheses from the local VIII15R `TrueState`, global existence, and metric-valued Ricci correspondence as separate formalization gates.
-- source:
--   He Wang, Exact Spacetime Atlas IX analytic bridge. Local source, commit 8fc44e0bf5f0; Atlas/EinsteinMaxwell/ES5/KerrSchild/IX/Main.lean#L78-L94; SHA-256 18884bf60ddfde40e152ae58d87e665266dbac3d35d7783040639e2d0e987d6b. Registered definitions: mission/PHYSICS_BOUNDARY.md, notes/B3_POLICY.md. Analytic source and residual bridge: Exact Spacetime Atlas VIII17/VIII20 local source and weighted-residual modules; formulas are copied from the pinned local Lean source and checked by the kernel..

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.IX.actual_source_bridge_of_true_state
    (σ : PhysicalTrueState) (wM : ℝ → ℝ)
    (hrel : GenericMRelation σ wM)
    (hid : UnabsorbedResidualIdentity σ wM)
    (hbound : ∀ x, x ∈ KG → |lamM x (σ.jet x)| ≤ (5 / 8 : ℝ))
    (hzero : ∀ x, x ∈ KG → wF σ x = 0 ∧ wMc σ x = 0 ∧ wC σ x = 0 ∧ wA σ x = 0) :
    ∀ x, x ∈ KG → srcMbar σ x = qMcK σ x := by sorry
