-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_mag_unique
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII04.mag_unique
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-11T13:28:43.45123+00:00
-- url     : https://prove2.me/theorems/9081bd7b-5dd2-40fe-afb2-c5a53e549ca4
-- title:
--   Supporting lemma: VIII04.mag_unique
-- statement:
--   For real Q,j and 0<=Ri<Rh, any b1,b2 in MagClass(Rh) satisfying Lop(Rh,Ri,Q)(b)(R)=2*Q*j/R^3 for all R>Rh agree on (Rh,infinity). No charge gate is assumed in this theorem.
--
--   Scope: This node asserts exactly its displayed Lean statement with every hypothesis retained. Its role in Atlas VIII does not narrow more general supporting results to the fixed RN anchor. The project does not establish a finite-rotation spacetime, extension of such a spacetime through a horizon, or a normalized physical magnetic moment. Radial endpoint extensions proved in the displayed theorems are retained. No literature priority is claimed.
-- source:
--   Project formalization, frozen source commit 323deba9a80475cfd477eb35bd415aa9d2dc18ff; Atlas/EinsteinMaxwell/ES5/KerrSchild/VIII04/BVP.lean, lines 166-237; SHA-256 3a19830097cbcfc7f923ed609ab1046deeafccc2d34dd9b5a4bb9c7792670c76. No public repository URL is claimed. Background radial equations: Froeb et al., EPJC 82 (2022) 215, https://arxiv.org/abs/2112.13266 (background citation, not a claimed source of this exact formal theorem).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII04.mag_unique {Rh Ri Q j : ℝ} (hRi : 0 ≤ Ri) (hlt : Ri < Rh) {b1 b2 : ℝ → ℝ}
    (h1 : MagClass Rh b1) (h2 : MagClass Rh b2)
    (e1 : ∀ R ∈ Ioi Rh, Lop Rh Ri Q b1 R = 2 * Q * j / R ^ 3)
    (e2 : ∀ R ∈ Ioi Rh, Lop Rh Ri Q b2 R = 2 * Q * j / R ^ 3) : EqOn b1 b2 (Ioi Rh) := by sorry
