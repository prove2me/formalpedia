-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_viii08_main
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII08.viii08_main
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-11T13:33:28.926982+00:00
-- url     : https://prove2.me/theorems/2faadcc3-487f-42c1-a4b1-92649c7e79a5
-- title:
--   Supporting lemma: VIII08.viii08_main
-- statement:
--   Assume q is C1 on U, |q(x)|<=Aq for every x in K, Aq>=0, r is continuous on U, |r(x)|<=Ar for every x in K, Ar>=0, where U=(-1/12,5/12) and K=[0,1/3]. Let b=bfun(j,q), v=vfun(j,q,r), B=3|j|+Aq. Then b belongs to MagClass(3), v to VClass(3), and for every R>3: Lmag(b)(R)=sfun(j,q)(1/R)/R^3; Dell(j,b,v)(R)=r(1/R)/R; |R*b(R)|<=B/8; |R^2*b'(R)|<=B; |R^3*(v(R)-j/R^2)|<=B/4+Ar/3; |R^4*(v'(R)+2*j/R^3)|<=3*B/4+Ar. As R tends to infinity, R*b(R), R^2*v(R), R^3*(v(R)-j/R^2), and R^4*(v'(R)+2*j/R^3) tend respectively to sigmaB(j,q), j, 2*sigmaB(j,q)-r(0)/3, and r(0)-6*sigmaB(j,q).
--
--   Scope: This node asserts exactly its displayed Lean statement with every hypothesis retained. Its role in Atlas VIII does not narrow more general supporting results to the fixed RN anchor. The project does not establish a finite-rotation spacetime, extension of such a spacetime through a horizon, or a normalized physical magnetic moment. Radial endpoint extensions proved in the displayed theorems are retained. No literature priority is claimed.
-- source:
--   Project formalization, frozen source commit 323deba9a80475cfd477eb35bd415aa9d2dc18ff; Atlas/EinsteinMaxwell/ES5/KerrSchild/VIII08/Main.lean, lines 34-78; SHA-256 d01f0cd71897e3e09ff9ccd3f6e7f88441c68053daae8d41050e49959a247feb. No public repository URL is claimed. Background radial equations: Froeb et al., EPJC 82 (2022) 215, https://arxiv.org/abs/2112.13266 (background citation, not a claimed source of this exact formal theorem).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII08.viii08_main {j Aq Ar : ℝ} {q r : ℝ → ℝ}
    (hqc : ContDiffOn ℝ 1 q UG) (hq : ∀ x ∈ KG, |q x| ≤ Aq) (hAq : 0 ≤ Aq)
    (hr : ContinuousOn r UG) (hrb : ∀ x ∈ KG, |r x| ≤ Ar) (hAr : 0 ≤ Ar) :
    -- the magnetic potential solves the actual equation and lies in `MagClass 3`
    (MagClass 3 (bfun j q) ∧ ∀ R ∈ Ioi (3:ℝ), Lmag (bfun j q) R = sfun j q (1 / R) / R ^ 3)
    -- the sharp value and derivative bounds hold on all of `I`
    ∧ (∀ R : ℝ, 3 < R → |R * bfun j q R| ≤ (3 * |j| + Aq) / 8)
    ∧ (∀ R : ℝ, 3 < R → |R ^ 2 * deriv (bfun j q) R| ≤ 3 * |j| + Aq)
    -- the rotation solves the actual angular-momentum equation and lies in `VClass 3`
    ∧ (VClass 3 (vfun j q r) ∧ ∀ R ∈ Ioi (3:ℝ), Dell j (bfun j q) (vfun j q r) R = r (1 / R) / R)
    -- the rotation bounds
    ∧ (∀ R : ℝ, 3 < R → |R ^ 3 * (vfun j q r R - j / R ^ 2)| ≤ (3 * |j| + Aq) / 4 + Ar / 3)
    ∧ (∀ R : ℝ, 3 < R → |R ^ 4 * (deriv (vfun j q r) R + 2 * j / R ^ 3)|
        ≤ 3 * (3 * |j| + Aq) / 4 + Ar)
    -- the four far-field limits
    ∧ Tendsto (fun R : ℝ => R * bfun j q R) atTop (𝓝 (sigmaB j q))
    ∧ Tendsto (fun R : ℝ => R ^ 2 * vfun j q r R) atTop (𝓝 j)
    ∧ Tendsto (fun R : ℝ => R ^ 3 * (vfun j q r R - j / R ^ 2)) atTop
        (𝓝 (2 * sigmaB j q - r 0 / 3))
    ∧ Tendsto (fun R : ℝ => R ^ 4 * (deriv (vfun j q r) R + 2 * j / R ^ 3)) atTop
        (𝓝 (r 0 - 6 * sigmaB j q)) := by sorry
