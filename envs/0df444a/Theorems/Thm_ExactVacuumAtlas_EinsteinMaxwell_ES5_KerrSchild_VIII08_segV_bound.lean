-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_segV_bound
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII08.segV_bound
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-11T13:27:56.459654+00:00
-- url     : https://prove2.me/theorems/ed6ad780-d9b5-4bdf-8a5a-f857d8644371
-- title:
--   Supporting lemma: VIII08.segV_bound
-- statement:
--   For t>=3, if |hg(s)|<=B for every s in [3,t], then |segV(hg)(t)|<=(2/3)*B.
--
--   Scope: This node asserts exactly its displayed Lean statement with every hypothesis retained. Its role in Atlas VIII does not narrow more general supporting results to the fixed RN anchor. The project does not establish a finite-rotation spacetime, extension of such a spacetime through a horizon, or a normalized physical magnetic moment. Radial endpoint extensions proved in the displayed theorems are retained. No literature priority is claimed.
-- source:
--   Project formalization, frozen source commit 323deba9a80475cfd477eb35bd415aa9d2dc18ff; Atlas/EinsteinMaxwell/ES5/KerrSchild/VIII08/Picard.lean, lines 282-302; SHA-256 d578155f694b71182849b0762856b4b8a2f33e946c95905a68a3a725bab836a6. No public repository URL is claimed. Background radial equations: Froeb et al., EPJC 82 (2022) 215, https://arxiv.org/abs/2112.13266 (background citation, not a claimed source of this exact formal theorem).

import Mathlib
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PaperGauge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VII18RationalClass
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_BVP
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_Background
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII04_Linearize
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Ops
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VIII08_Picard
open Set Filter Topology MeasureTheory intervalIntegral
open scoped ContDiff Interval
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII08
set_option maxHeartbeats 2000000
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII04

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VIII08.segV_bound {hg : ℝ → ℝ} {t B : ℝ} (ht : 3 ≤ t)
    (hB : ∀ s ∈ Icc 3 t, |hg s| ≤ B) :
    |segV hg t| ≤ 2 / 3 * B := by sorry
