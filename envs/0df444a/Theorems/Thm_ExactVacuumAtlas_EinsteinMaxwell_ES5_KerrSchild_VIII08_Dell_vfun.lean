-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Dell_vfun
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII08.Dell_vfun
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-11T13:33:04.51836+00:00
-- url     : https://prove2.me/theorems/7e2f053b-60f8-432f-b7f5-4989e1bcdd9a
-- title:
--   Supporting lemma: VIII08.Dell_vfun
-- statement:
--   Assume q is C1 on U, |q(x)|<=Aq for every x in K, Aq>=0, r is continuous on U, where U=(-1/12,5/12) and K=[0,1/3]. For every R>3, Dell(j,bfun(j,q),vfun(j,q,r))(R)=r(1/R)/R.
--
--   Scope: This node asserts exactly its displayed Lean statement with every hypothesis retained. Its role in Atlas VIII does not narrow more general supporting results to the fixed RN anchor. The project does not establish a finite-rotation spacetime, extension of such a spacetime through a horizon, or a normalized physical magnetic moment. Radial endpoint extensions proved in the displayed theorems are retained. No literature priority is claimed.
-- source:
--   Project formalization, frozen source commit 323deba9a80475cfd477eb35bd415aa9d2dc18ff; Atlas/EinsteinMaxwell/ES5/KerrSchild/VIII08/Rot.lean, lines 227-246; SHA-256 dfd5dd7fba234da38fe66302add1620f5e75b7f4fcf721e03fb85769716d49b5. No public repository URL is claimed. Background radial equations: Froeb et al., EPJC 82 (2022) 215, https://arxiv.org/abs/2112.13266 (background citation, not a claimed source of this exact formal theorem).

import Mathlib
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PaperGauge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VII18RationalClass
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_BVP
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_Background
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_Linearize
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_Main
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII05_Anchor
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Class
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Compact
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Fixed
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Green
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Growth
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_MagClass
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Ops
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Picard
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Rot
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Sum
open Set Filter Topology MeasureTheory intervalIntegral
open scoped ContDiff Interval
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII08
set_option maxHeartbeats 4000000
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII04
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII05

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII08.Dell_vfun {j Aq : ℝ} {q r : ℝ → ℝ} (hqc : ContDiffOn ℝ 1 q UG)
    (hq : ∀ x ∈ KG, |q x| ≤ Aq) (hAq : 0 ≤ Aq) (hr : ContinuousOn r UG) {R : ℝ} (hR : 3 < R) :
    Dell j (bfun j q) (vfun j q r) R = r (1 / R) / R := by sorry
