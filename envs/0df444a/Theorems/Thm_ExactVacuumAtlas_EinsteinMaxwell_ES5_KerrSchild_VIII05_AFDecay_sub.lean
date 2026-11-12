-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_VIII05_AFDecay_sub
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII05.AFDecay.sub
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-11T13:28:15.189958+00:00
-- url     : https://prove2.me/theorems/f0dd9029-c6ff-4c23-9fff-51c1d7e68470
-- title:
--   Supporting lemma: VIII05.AFDecay.sub
-- statement:
--   If u1,u2 are C1 on (Rh,infinity) and both satisfy AFDecay(Rh), then u1-u2 satisfies AFDecay(Rh).
--
--   Scope: This node asserts exactly its displayed Lean statement with every hypothesis retained. Its role in Atlas VIII does not narrow more general supporting results to the fixed RN anchor. The project does not establish a finite-rotation spacetime, extension of such a spacetime through a horizon, or a normalized physical magnetic moment. Radial endpoint extensions proved in the displayed theorems are retained. No literature priority is claimed.
-- source:
--   Project formalization, frozen source commit 323deba9a80475cfd477eb35bd415aa9d2dc18ff; Atlas/EinsteinMaxwell/ES5/KerrSchild/VIII05/BVP.lean, lines 98-120; SHA-256 9eb8c11486fc4e20ff71f559a5d2311257188f4a883f263e76a7173713a2ef1d. No public repository URL is claimed. Background radial equations: Froeb et al., EPJC 82 (2022) 215, https://arxiv.org/abs/2112.13266 (background citation, not a claimed source of this exact formal theorem).

import Mathlib
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PaperGauge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VII18RationalClass
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_BVP
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_Background
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_Linearize
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_Main
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII05_Anchor
open Set Filter Topology
open scoped ContDiff
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII05
set_option maxHeartbeats 4000000
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII04

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII05.AFDecay.sub {Rh : ℝ} {u1 u2 : ℝ → ℝ} (h1 : ContDiffOn ℝ 1 u1 (Ioi Rh))
    (h2 : ContDiffOn ℝ 1 u2 (Ioi Rh)) (a1 : AFDecay Rh u1) (a2 : AFDecay Rh u2) :
    AFDecay Rh (fun s => u1 s - u2 s) := by sorry
