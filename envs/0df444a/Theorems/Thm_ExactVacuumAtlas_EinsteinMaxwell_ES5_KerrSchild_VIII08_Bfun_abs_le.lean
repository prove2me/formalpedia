-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Bfun_abs_le
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII08.Bfun_abs_le
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-11T13:30:22.911546+00:00
-- url     : https://prove2.me/theorems/d6f8053b-8d30-4b2f-b7ee-b328214b3942
-- title:
--   Supporting lemma: VIII08.Bfun_abs_le
-- statement:
--   Assume |q(x)|<=Aq for every x in K, Aq>=0, where U=(-1/12,5/12) and K=[0,1/3]. For every x in K, |Bfun(j,q)(x)|<=(9/16)*(3|j|+Aq). No continuity of q is assumed.
--
--   Scope: This node asserts exactly its displayed Lean statement with every hypothesis retained. Its role in Atlas VIII does not narrow more general supporting results to the fixed RN anchor. The project does not establish a finite-rotation spacetime, extension of such a spacetime through a horizon, or a normalized physical magnetic moment. Radial endpoint extensions proved in the displayed theorems are retained. No literature priority is claimed.
-- source:
--   Project formalization, frozen source commit 323deba9a80475cfd477eb35bd415aa9d2dc18ff; Atlas/EinsteinMaxwell/ES5/KerrSchild/VIII08/Bounds.lean, lines 49-79; SHA-256 2c39ad85c03cfe944898849f6523b1b3ad74336bbd3b8eaecb853d5c4bb13c3c. No public repository URL is claimed. Background radial equations: Froeb et al., EPJC 82 (2022) 215, https://arxiv.org/abs/2112.13266 (background citation, not a claimed source of this exact formal theorem).

import Mathlib
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PaperGauge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VII18RationalClass
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_BVP
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_Background
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_Linearize
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Compact
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Fixed
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Green
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Growth
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Ops
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Picard
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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII08.Bfun_abs_le {j Aq : ℝ} {q : ℝ → ℝ} (hq : ∀ x ∈ KG, |q x| ≤ Aq) (hAq : 0 ≤ Aq)
    {x : ℝ} (hx : x ∈ KG) : |Bfun j q x| ≤ 9 / 16 * (3 * |j| + Aq) := by sorry
