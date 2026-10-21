-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_hasDerivAt_einsteinMaxwell_of
-- name    : ExactVacuumAtlas.Variation.hasDerivAt_einsteinMaxwell_of
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:39.515844+00:00
-- url     : https://prove2.me/theorems/75e95971-9308-47e0-8402-a4e00f6b7f69
-- title:
--   Pointwise derivative of E from its ingredients
-- statement:
--   Pointwise derivative of E from its ingredients
--
--   Given HasDerivAt at 0 of g, ricciOf, ricciScalar and emStress components at y, the ε-derivative of E_ab at y is LE_ab (product rule on the finite expression).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** E 的导数（由组成部分导数推出）。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Bridge.lean#L125-L132; SHA-256 c0401e780ed4e7fdf93b3fceb547d092276cb438ae1a341a5d661c712a8a09c4. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Defs
import Definitions.Def_Atlas_Transport_MatrixCalc
open Filter Topology
open scoped ContDiff
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas
open ExactVacuumAtlas.Variation
variable {n : ℕ}
variable {g ginv : ℝ → Metric 4} {F : ℝ → TwoForm 4} {h : Metric 4} {f : TwoForm 4} {y : Pt 4}

theorem ExactVacuumAtlas.Variation.hasDerivAt_einsteinMaxwell_of (hg : ∀ i j, HasDerivAt (fun ε => g ε i j y) (h i j y) 0)
    (hRic : ∀ a b, HasDerivAt (fun ε => ricciOf (g ε) (ginv ε) a b y) (ricciVar (g 0) (ginv 0) h a b y) 0)
    (hR : HasDerivAt (fun ε => ricciScalar (g ε) (ginv ε) y) (scalarVar (g 0) (ginv 0) h y) 0)
    (hS : ∀ a b, HasDerivAt (fun ε => emStress (g ε) (ginv ε) (F ε) a b y)
      (emStressVar (g 0) (ginv 0) h (F 0) f a b y) 0) (a b : Fin 4) :
    HasDerivAt (fun ε => einsteinMaxwell (g ε) (ginv ε) (F ε) a b y)
      (linEinstein (g 0) (ginv 0) (F 0) h f a b y) 0 := by sorry
