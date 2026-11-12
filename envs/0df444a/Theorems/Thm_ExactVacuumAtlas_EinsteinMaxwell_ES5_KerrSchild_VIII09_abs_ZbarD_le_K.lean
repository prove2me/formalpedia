-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_VIII09_abs_ZbarD_le_K
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII09.abs_ZbarD_le_K
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-11T13:33:29.89035+00:00
-- url     : https://prove2.me/theorems/95da984c-3cab-4bb9-82cc-a574e3251d74
-- title:
--   Supporting lemma: VIII09.abs_ZbarD_le_K
-- statement:
--   For every x in K=[0,1/3], |ZbarD(x)|<=35/64.
--
--   Scope: This node asserts exactly its displayed Lean statement with every hypothesis retained. Its role in Atlas VIII does not narrow more general supporting results to the fixed RN anchor. The project does not establish a finite-rotation spacetime, extension of such a spacetime through a horizon, or a normalized physical magnetic moment. Radial endpoint extensions proved in the displayed theorems are retained. No literature priority is claimed.
-- source:
--   Project formalization, frozen source commit 323deba9a80475cfd477eb35bd415aa9d2dc18ff; Atlas/EinsteinMaxwell/ES5/KerrSchild/VIII09/Bounds.lean, lines 266-300; SHA-256 c31adb116aea578a982bceaf0a9fa2055f0145b3ef83e371820ce1e87fc30130. No public repository URL is claimed. Background radial equations: Froeb et al., EPJC 82 (2022) 215, https://arxiv.org/abs/2112.13266 (background citation, not a claimed source of this exact formal theorem).

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
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Limits
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_MagClass
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Ops
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Picard
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Rot
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Sigma
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Sum
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII09_Compact
open Set Filter Topology MeasureTheory intervalIntegral
open scoped ContDiff Interval
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII09
set_option maxHeartbeats 1600000
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII04
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII05
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII08

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII09.abs_ZbarD_le_K {x : ℝ} (hx : x ∈ KG) : |ZbarD x| ≤ 35 / 64 := by sorry
