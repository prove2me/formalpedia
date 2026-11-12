-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_Lop_c_div
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII04.Lop_c_div
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-11T13:27:52.415455+00:00
-- url     : https://prove2.me/theorems/a976057d-9f10-4771-9484-9b2d574130c8
-- title:
--   Supporting lemma: VIII04.Lop_c_div
-- statement:
--   Let Rh,Ri,Q be real with Q^2=3*Rh*Ri/4. For every real c and R!=0, Lop(Rh,Ri,Q)(x -> c/x)(R)=2*n1(Rh,Ri)*c/R^3. No ordering of Rh,Ri is required.
--
--   Scope: This node asserts exactly its displayed Lean statement with every hypothesis retained. Its role in Atlas VIII does not narrow more general supporting results to the fixed RN anchor. The project does not establish a finite-rotation spacetime, extension of such a spacetime through a horizon, or a normalized physical magnetic moment. Radial endpoint extensions proved in the displayed theorems are retained. No literature priority is claimed.
-- source:
--   Project formalization, frozen source commit 323deba9a80475cfd477eb35bd415aa9d2dc18ff; Atlas/EinsteinMaxwell/ES5/KerrSchild/VIII04/Main.lean, lines 83-99; SHA-256 702525fb743224269bfa838194191604d366d6b06ef85d287c95841358c54223. No public repository URL is claimed. Background radial equations: Froeb et al., EPJC 82 (2022) 215, https://arxiv.org/abs/2112.13266 (background citation, not a claimed source of this exact formal theorem).

import Mathlib
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PaperGauge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VII18RationalClass
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_BVP
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_Background
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_Linearize
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_Main
open Set Filter Topology
open scoped ContDiff
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII04
set_option maxHeartbeats 1000000
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII04.Lop_c_div {Rh Ri Q : ℝ} (hQ : Q ^ 2 = 3 * Rh * Ri / 4) (c : ℝ) {R : ℝ} (hR : R ≠ 0) :
    Lop Rh Ri Q (fun x => c / x) R = 2 * n1 Rh Ri * c / R ^ 3 := by sorry
