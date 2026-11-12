-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_VIII08R_pair_unique
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII08R.pair_unique
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-11T13:33:49.288476+00:00
-- url     : https://prove2.me/theorems/69790413-ac3b-4ad8-9a56-9f0f9800d90a
-- title:
--   Supporting lemma: VIII08R.pair_unique
-- statement:
--   Assume q is C1 on U, r is continuous on U, where U=(-1/12,5/12) and K=[0,1/3]. If b0 belongs to MagClass(3), v0 to VClass(3), and Lmag(b0)(R)=sfun(j,q)(1/R)/R^3 and Dell(j,b0,v0)(R)=r(1/R)/R for every R>3, then b0=bfun(j,q) and v0=vfun(j,q,r) on (3,infinity). Both class assumptions remain required.
--
--   Scope: This node asserts exactly its displayed Lean statement with every hypothesis retained. Its role in Atlas VIII does not narrow more general supporting results to the fixed RN anchor. The project does not establish a finite-rotation spacetime, extension of such a spacetime through a horizon, or a normalized physical magnetic moment. Radial endpoint extensions proved in the displayed theorems are retained. No literature priority is claimed.
-- source:
--   Project formalization, frozen source commit 323deba9a80475cfd477eb35bd415aa9d2dc18ff; Atlas/EinsteinMaxwell/ES5/KerrSchild/VIII08R/Pair.lean, lines 91-120; SHA-256 81cc8aa586e399b20c41db2c7d4352d1aee3ce653f22f71c279137822b19dc55. No public repository URL is claimed. Background radial equations: Froeb et al., EPJC 82 (2022) 215, https://arxiv.org/abs/2112.13266 (background citation, not a claimed source of this exact formal theorem).

import Mathlib
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PaperGauge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VII18RationalClass
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_BVP
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_Background
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_Linearize
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_Main
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII05_Anchor
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08R_Pair
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Class
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Compact
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Fixed
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Green
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Growth
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Limits
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_MagClass
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Ops
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Picard
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Rot
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Sigma
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Sum
open Set Filter Topology MeasureTheory intervalIntegral
open scoped ContDiff Interval
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII08R
set_option maxHeartbeats 4000000
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII04
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII05
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII08

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII08R.pair_unique {j : ℝ} {q r : ℝ → ℝ} (hqc : ContDiffOn ℝ 1 q UG)
    (hr : ContinuousOn r UG) {b0 v0 : ℝ → ℝ}
    (hb : MagClass 3 b0) (hv : VClass 3 v0)
    (hL : ∀ R ∈ Ioi (3:ℝ), Lmag b0 R = sfun j q (1 / R) / R ^ 3)
    (hD : ∀ R ∈ Ioi (3:ℝ), Dell j b0 v0 R = r (1 / R) / R) :
    EqOn b0 (bfun j q) (Ioi (3:ℝ)) ∧ EqOn v0 (vfun j q r) (Ioi (3:ℝ)) := by sorry
