-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_hasDerivAt_maxwellDiv_of
-- name    : ExactVacuumAtlas.Variation.hasDerivAt_maxwellDiv_of
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:39.099427+00:00
-- url     : https://prove2.me/theorems/b5c0da19-aefd-4398-ae09-28ea7c2a3c31
-- title:
--   Pointwise derivative of J
-- statement:
--   Pointwise derivative of J
--
--   Given the ε-derivatives of the Christoffel symbols (chrVar), of F^{ab} (raise2Var) and of ∂F^{ab} at y, the derivative of J^b at y is LJ^b.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** J 的导数。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Bridge.lean#L93-L100; SHA-256 c0401e780ed4e7fdf93b3fceb547d092276cb438ae1a341a5d661c712a8a09c4. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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
variable {g ginv : ℝ → Metric n} {F : ℝ → TwoForm n} {h : Metric n} {f : TwoForm n} {y : Pt n}

theorem ExactVacuumAtlas.Variation.hasDerivAt_maxwellDiv_of
    (hΓ : ∀ a b c, HasDerivAt (fun ε => christoffel (g ε) (ginv ε) a b c y) (chrVar (g 0) (ginv 0) h a b c y) 0)
    (hU : ∀ a b, HasDerivAt (fun ε => raise2 (ginv ε) (F ε) a b y) (raise2Var (ginv 0) h (F 0) f a b y) 0)
    (hpU : ∀ a b, HasDerivAt (fun ε => pd a (raise2 (ginv ε) (F ε) a b) y)
      (pd a (raise2Var (ginv 0) h (F 0) f a b) y) 0) (b : Fin n) :
    HasDerivAt (fun ε => maxwellDiv (g ε) (ginv ε) (F ε) b y) (linMaxwell (g 0) (ginv 0) (F 0) h f b y) 0 := by sorry
