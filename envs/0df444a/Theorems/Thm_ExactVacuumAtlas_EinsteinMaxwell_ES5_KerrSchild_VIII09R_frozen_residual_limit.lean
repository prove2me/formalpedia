-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_VIII09R_frozen_residual_limit
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII09R.frozen_residual_limit
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-11T13:38:05.166683+00:00
-- url     : https://prove2.me/theorems/416d2c66-b58a-4b95-9408-0fd1b2df6882
-- title:
--   Supporting lemma: VIII09R.frozen_residual_limit
-- statement:
--   For every real j and fixed R>3, the actual Maxwell residual on (fE,mE,N0(3,1),aFrozen), Q=3/2, J=epsilon*j, divided by epsilon^3, tends to -P(R)*q3j(j,1/R)/R^3 as epsilon tends to zero through nonzero values. Only the cubic magnetic correction is frozen; fE,mE retain quadratic terms.
--
--   Scope: This node asserts exactly its displayed Lean statement with every hypothesis retained. Its role in Atlas VIII does not narrow more general supporting results to the fixed RN anchor. The project does not establish a finite-rotation spacetime, extension of such a spacetime through a horizon, or a normalized physical magnetic moment. Radial endpoint extensions proved in the displayed theorems are retained. No literature priority is claimed.
-- source:
--   Project formalization, frozen source commit 323deba9a80475cfd477eb35bd415aa9d2dc18ff; Atlas/EinsteinMaxwell/ES5/KerrSchild/VIII09R/Frozen.lean, lines 162-192; SHA-256 6b6b65223be433bea5c87aa9e5929846cf17ce0ddf36181a237a6ec1359e318b. No public repository URL is claimed. Background radial equations: Froeb et al., EPJC 82 (2022) 215, https://arxiv.org/abs/2112.13266 (background citation, not a claimed source of this exact formal theorem).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII09R.frozen_residual_limit (j : ℝ) {R : ℝ} (hR : 3 < R) :
    Tendsto (fun ε : ℝ =>
        VII18.maxwellResidual (fE j ε) (mE j ε) (N0 3 1) (aFrozen j ε) (3 / 2) (ε * j) R
          / ε ^ 3)
      (𝓝[≠] (0:ℝ)) (𝓝 (-(P R * (q3j j (1 / R) / R ^ 3)))) := by sorry
