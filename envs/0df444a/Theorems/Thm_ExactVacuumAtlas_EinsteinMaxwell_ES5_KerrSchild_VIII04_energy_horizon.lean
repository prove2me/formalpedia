-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_energy_horizon
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII04.energy_horizon
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-11T13:27:52.915572+00:00
-- url     : https://prove2.me/theorems/ab1063b1-e6b8-4d4b-b0b2-9f484ad576ea
-- title:
--   Supporting lemma: VIII04.energy_horizon
-- statement:
--   For Rh>0, real Ri, and h satisfying HorizonC1(Rh,h), energy(Rh,Ri,h)(R) tends to zero as R tends to Rh from above. HorizonC1 is the specified local C1 extension condition, not a nonlinear spacetime claim.
--
--   Scope: This node asserts exactly its displayed Lean statement with every hypothesis retained. Its role in Atlas VIII does not narrow more general supporting results to the fixed RN anchor. The project does not establish a finite-rotation spacetime, extension of such a spacetime through a horizon, or a normalized physical magnetic moment. Radial endpoint extensions proved in the displayed theorems are retained. No literature priority is claimed.
-- source:
--   Project formalization, frozen source commit 323deba9a80475cfd477eb35bd415aa9d2dc18ff; Atlas/EinsteinMaxwell/ES5/KerrSchild/VIII04/BVP.lean, lines 116-136; SHA-256 3a19830097cbcfc7f923ed609ab1046deeafccc2d34dd9b5a4bb9c7792670c76. No public repository URL is claimed. Background radial equations: Froeb et al., EPJC 82 (2022) 215, https://arxiv.org/abs/2112.13266 (background citation, not a claimed source of this exact formal theorem).

import Mathlib
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PaperGauge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VII18RationalClass
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_BVP
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_Background
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_Linearize
open Set Filter Topology
open scoped ContDiff
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII04
set_option maxHeartbeats 1000000

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII04.energy_horizon {Rh Ri : ℝ} (hRh : 0 < Rh) {h : ℝ → ℝ} (hh : HorizonC1 Rh h) :
    Tendsto (energy Rh Ri h) (𝓝[>] Rh) (𝓝 0) := by sorry
