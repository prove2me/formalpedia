-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_hasDerivAt_emStress_of
-- name    : ExactVacuumAtlas.Variation.hasDerivAt_emStress_of
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:34.909014+00:00
-- url     : https://prove2.me/theorems/c091d9fc-dcc2-4920-b7d5-d46ac845352e
-- title:
--   Pointwise derivative of the Maxwell stress
-- statement:
--   Pointwise derivative of the Maxwell stress
--
--   Given the ε-derivatives of g, ginv (= invVar), F and fieldSq at y, the derivative of S_ab at y is emStressVar.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 应力张量的导数。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Bridge.lean#L113-L123; SHA-256 c0401e780ed4e7fdf93b3fceb547d092276cb438ae1a341a5d661c712a8a09c4. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.Variation.hasDerivAt_emStress_of (hg : ∀ i j, HasDerivAt (fun ε => g ε i j y) (h i j y) 0)
    (hgi : ∀ i j, HasDerivAt (fun ε => ginv ε i j y) (invVar (ginv 0) h i j y) 0)
    (hF : ∀ i j, HasDerivAt (fun ε => F ε i j y) (f i j y) 0)
    (hs : HasDerivAt (fun ε => fieldSq (ginv ε) (F ε) y) (fieldSqVar (ginv 0) h (F 0) f y) 0) (a b : Fin 4) :
    HasDerivAt (fun ε => emStress (g ε) (ginv ε) (F ε) a b y) (emStressVar (g 0) (ginv 0) h (F 0) f a b y) 0 := by sorry
