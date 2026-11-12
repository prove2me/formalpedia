-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_VIII09_pair_unique_cubic
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII09.pair_unique_cubic
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-11T13:35:42.604965+00:00
-- url     : https://prove2.me/theorems/c5a9213c-b05d-4371-b793-c1803462e608
-- title:
--   Uniqueness of the cubic response on the exterior
-- statement:
--   In the fixed pure five-dimensional Einstein-Maxwell equal-spin radial setting with Lambda=0, no Chern-Simons term, RN anchor (3,1,3/2), and exterior R>3, for every real j, any pair c,d in MagClass 3 and VClass 3 satisfying Lmag(c)(R)=q3j(j,1/R)/R^3 and Dell(0,c,d)(R)=r3j(j,1/R)/R for all R>3 agrees with c_j,d_j at every R>3.
--
--   Scope: This node asserts exactly its displayed Lean statement with every hypothesis retained. Its role in Atlas VIII does not narrow more general supporting results to the fixed RN anchor. The project does not establish a finite-rotation spacetime, extension of such a spacetime through a horizon, or a normalized physical magnetic moment. Radial endpoint extensions proved in the displayed theorems are retained. No literature priority is claimed.
-- source:
--   Project formalization, frozen source commit 323deba9a80475cfd477eb35bd415aa9d2dc18ff; Atlas/EinsteinMaxwell/ES5/KerrSchild/VIII09/Solve.lean, lines 124-135; SHA-256 3cdb9bf0bed3bd75a053bcb79d76acc4e5bb541f00b3ad9aa9d4278dc79a6e17. No public repository URL is claimed. Background radial equations: Froeb et al., EPJC 82 (2022) 215, https://arxiv.org/abs/2112.13266 (background citation, not a claimed source of this exact formal theorem).

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
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII09_Compact
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII09_Derivation
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII09_Solve
open Set Filter Topology MeasureTheory intervalIntegral
open scoped ContDiff Interval Topology
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII09
set_option maxHeartbeats 2000000
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII04
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII05
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII08
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII08R

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII09.pair_unique_cubic (j : ℝ) {c d : ℝ → ℝ}
    (hc : MagClass 3 c) (hd : VClass 3 d)
    (hcEq : ∀ R ∈ Ioi (3:ℝ), Lmag c R = q3j j (1 / R) / R ^ 3)
    (hdEq : ∀ R ∈ Ioi (3:ℝ), Dell 0 c d R = r3j j (1 / R) / R) :
    EqOn c (cj j) (Ioi (3:ℝ)) ∧ EqOn d (dj j) (Ioi (3:ℝ)) := by sorry
