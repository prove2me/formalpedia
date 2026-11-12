-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_Lop_sub
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII04.Lop_sub
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-11T13:27:49.249996+00:00
-- url     : https://prove2.me/theorems/3416646d-bf01-4094-bca0-0b3a65afe1e6
-- title:
--   Supporting lemma: VIII04.Lop_sub
-- statement:
--   For real Rh,Ri,Q with Rh>=0 and b1,b2 C2 on (Rh,infinity), Lop(Rh,Ri,Q)(b1-b2)(R)=Lop(Rh,Ri,Q)(b1)(R)-Lop(Rh,Ri,Q)(b2)(R) for every R>Rh.
--
--   Scope: This node asserts exactly its displayed Lean statement with every hypothesis retained. Its role in Atlas VIII does not narrow more general supporting results to the fixed RN anchor. The project does not establish a finite-rotation spacetime, extension of such a spacetime through a horizon, or a normalized physical magnetic moment. Radial endpoint extensions proved in the displayed theorems are retained. No literature priority is claimed.
-- source:
--   Project formalization, frozen source commit 323deba9a80475cfd477eb35bd415aa9d2dc18ff; Atlas/EinsteinMaxwell/ES5/KerrSchild/VIII04/BVP.lean, lines 60-83; SHA-256 3a19830097cbcfc7f923ed609ab1046deeafccc2d34dd9b5a4bb9c7792670c76. No public repository URL is claimed. Background radial equations: Froeb et al., EPJC 82 (2022) 215, https://arxiv.org/abs/2112.13266 (background citation, not a claimed source of this exact formal theorem).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII04.Lop_sub (Rh Ri Q : ℝ) {b1 b2 : ℝ → ℝ} (hb1 : ContDiffOn ℝ 2 b1 (Ioi Rh))
    (hb2 : ContDiffOn ℝ 2 b2 (Ioi Rh)) (hRh : 0 ≤ Rh) {R : ℝ} (hR : R ∈ Ioi Rh) :
    Lop Rh Ri Q (fun s => b1 s - b2 s) R = Lop Rh Ri Q b1 R - Lop Rh Ri Q b2 R := by sorry
