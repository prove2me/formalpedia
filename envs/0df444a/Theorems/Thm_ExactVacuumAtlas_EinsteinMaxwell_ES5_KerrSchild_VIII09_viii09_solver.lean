-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_VIII09_viii09_solver
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII09.viii09_solver
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-11T13:35:34.822308+00:00
-- url     : https://prove2.me/theorems/da62aae1-1075-4fe5-81dd-cf667ad7b8aa
-- title:
--   Constructed cubic response and four asymptotic limits
-- statement:
--   In the fixed pure five-dimensional Einstein-Maxwell equal-spin radial setting with Lambda=0, no Chern-Simons term, RN anchor (3,1,3/2), and exterior R>3, for every real j, the explicitly defined pair (c_j,d_j) belongs to MagClass 3 and VClass 3 and solves Lmag(c_j)(R)=q3j(j,1/R)/R^3 and Dell(0,c_j,d_j)(R)=r3j(j,1/R)/R. For every R>3 it satisfies |R*c_j(R)|<=|j|^3/8, |R^2*c_j'(R)|<=|j|^3, |R^3*d_j(R)|<=11*|j|^3/12, and |R^4*d_j'(R)|<=11*|j|^3/4. The following limits are as R tends to positive infinity: Its four limits are R*c_j -> sigma3(j), R^2*d_j -> 0, R^3*d_j -> 2*sigma3(j)-7*j^3/72, and R^4*d_j' -> 7*j^3/24-6*sigma3(j).
--
--   Scope: This node asserts exactly its displayed Lean statement with every hypothesis retained. Its role in Atlas VIII does not narrow more general supporting results to the fixed RN anchor. The project does not establish a finite-rotation spacetime, extension of such a spacetime through a horizon, or a normalized physical magnetic moment. Radial endpoint extensions proved in the displayed theorems are retained. No literature priority is claimed.
-- source:
--   Project formalization, frozen source commit 323deba9a80475cfd477eb35bd415aa9d2dc18ff; Atlas/EinsteinMaxwell/ES5/KerrSchild/VIII09/Solve.lean, lines 60-120; SHA-256 3cdb9bf0bed3bd75a053bcb79d76acc4e5bb541f00b3ad9aa9d4278dc79a6e17. No public repository URL is claimed. Background radial equations: Froeb et al., EPJC 82 (2022) 215, https://arxiv.org/abs/2112.13266 (background citation, not a claimed source of this exact formal theorem).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII09.viii09_solver (j : ℝ) :
    (MagClass 3 (cj j) ∧ ∀ R ∈ Ioi (3:ℝ), Lmag (cj j) R = q3j j (1 / R) / R ^ 3)
    ∧ (∀ R : ℝ, 3 < R → |R * cj j R| ≤ |j| ^ 3 / 8)
    ∧ (∀ R : ℝ, 3 < R → |R ^ 2 * deriv (cj j) R| ≤ |j| ^ 3)
    ∧ (VClass 3 (dj j) ∧ ∀ R ∈ Ioi (3:ℝ), Dell 0 (cj j) (dj j) R = r3j j (1 / R) / R)
    ∧ (∀ R : ℝ, 3 < R → |R ^ 3 * dj j R| ≤ 11 * |j| ^ 3 / 12)
    ∧ (∀ R : ℝ, 3 < R → |R ^ 4 * deriv (dj j) R| ≤ 11 * |j| ^ 3 / 4)
    ∧ Tendsto (fun R : ℝ => R * cj j R) atTop (𝓝 (sigma3 j))
    ∧ Tendsto (fun R : ℝ => R ^ 2 * dj j R) atTop (𝓝 0)
    ∧ Tendsto (fun R : ℝ => R ^ 3 * dj j R) atTop (𝓝 (2 * sigma3 j - 7 * j ^ 3 / 72))
    ∧ Tendsto (fun R : ℝ => R ^ 4 * deriv (dj j) R) atTop (𝓝 (7 * j ^ 3 / 24 - 6 * sigma3 j)) := by sorry
