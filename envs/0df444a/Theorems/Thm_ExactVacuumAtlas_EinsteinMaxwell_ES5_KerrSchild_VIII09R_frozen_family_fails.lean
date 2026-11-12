-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_VIII09R_frozen_family_fails
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII09R.frozen_family_fails
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-11T13:38:02.013264+00:00
-- url     : https://prove2.me/theorems/af57b1d0-6602-43a4-b0b9-bae43f954d48
-- title:
--   A frozen magnetic correction leaves a nonzero cubic residual
-- statement:
--   In the fixed pure five-dimensional Einstein-Maxwell equal-spin radial setting with Lambda=0, no Chern-Simons term, RN anchor (3,1,3/2), and exterior R>3, for every nonzero real j there exists R>3 such that the actual Maxwell residual of the family aFrozen=epsilon*b1, retaining fE and mE, divided by epsilon^3 tends to the nonzero value -P(R)*q3j(j,1/R)/R^3.
--
--   Scope: This node asserts exactly its displayed Lean statement with every hypothesis retained. Its role in Atlas VIII does not narrow more general supporting results to the fixed RN anchor. The project does not establish a finite-rotation spacetime, extension of such a spacetime through a horizon, or a normalized physical magnetic moment. Radial endpoint extensions proved in the displayed theorems are retained. No literature priority is claimed.
-- source:
--   Project formalization, frozen source commit 323deba9a80475cfd477eb35bd415aa9d2dc18ff; Atlas/EinsteinMaxwell/ES5/KerrSchild/VIII09R/Frozen.lean, lines 196-212; SHA-256 6b6b65223be433bea5c87aa9e5929846cf17ce0ddf36181a237a6ec1359e318b. No public repository URL is claimed. Background radial equations: Froeb et al., EPJC 82 (2022) 215, https://arxiv.org/abs/2112.13266 (background citation, not a claimed source of this exact formal theorem).

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
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII09R_Frozen
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII09_Bridge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII09_Compact
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII09_Derivation
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII09_Ell
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII09_Solve
open Set Filter Topology MeasureTheory intervalIntegral
open scoped ContDiff Interval Topology
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII09R
set_option maxHeartbeats 3000000
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII04
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII05
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII08
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII08R
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII09

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII09R.frozen_family_fails (j : ℝ) (hj : j ≠ 0) :
    ∃ R : ℝ, 3 < R ∧ -(P R * (q3j j (1 / R) / R ^ 3)) ≠ 0 ∧
      Tendsto (fun ε : ℝ =>
          VII18.maxwellResidual (fE j ε) (mE j ε) (N0 3 1) (aFrozen j ε) (3 / 2) (ε * j) R
            / ε ^ 3)
        (𝓝[≠] (0:ℝ)) (𝓝 (-(P R * (q3j j (1 / R) / R ^ 3)))) := by sorry
