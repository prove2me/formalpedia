-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_energy_infinity
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII04.energy_infinity
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-11T13:27:52.018312+00:00
-- url     : https://prove2.me/theorems/9093a5b6-06b3-4526-bf5a-e8dff6c6ff82
-- title:
--   Supporting lemma: VIII04.energy_infinity
-- statement:
--   If 0<=Ri<Rh, C>=0, Rs>Rh, and |h(R)|<=C/R and |h'(R)|<=C/R^2 for every R>=Rs, then energy(Rh,Ri,h)(R) tends to zero as R tends to positive infinity.
--
--   Scope: This node asserts exactly its displayed Lean statement with every hypothesis retained. Its role in Atlas VIII does not narrow more general supporting results to the fixed RN anchor. The project does not establish a finite-rotation spacetime, extension of such a spacetime through a horizon, or a normalized physical magnetic moment. Radial endpoint extensions proved in the displayed theorems are retained. No literature priority is claimed.
-- source:
--   Project formalization, frozen source commit 323deba9a80475cfd477eb35bd415aa9d2dc18ff; Atlas/EinsteinMaxwell/ES5/KerrSchild/VIII04/BVP.lean, lines 146-164; SHA-256 3a19830097cbcfc7f923ed609ab1046deeafccc2d34dd9b5a4bb9c7792670c76. No public repository URL is claimed. Background radial equations: Froeb et al., EPJC 82 (2022) 215, https://arxiv.org/abs/2112.13266 (background citation, not a claimed source of this exact formal theorem).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII04.energy_infinity {Rh Ri : ℝ} (hRi : 0 ≤ Ri) (hlt : Ri < Rh) {h : ℝ → ℝ} {C Rs : ℝ}
    (hC : 0 ≤ C) (hRs : Rh < Rs) (hb : ∀ R ≥ Rs, |h R| ≤ C / R ∧ |deriv h R| ≤ C / R ^ 2) :
    Tendsto (energy Rh Ri h) atTop (𝓝 0) := by sorry
