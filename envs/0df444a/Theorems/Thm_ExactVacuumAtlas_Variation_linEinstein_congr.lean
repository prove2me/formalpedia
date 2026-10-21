-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_linEinstein_congr
-- name    : ExactVacuumAtlas.Variation.linEinstein_congr
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:42.387113+00:00
-- url     : https://prove2.me/theorems/2823e4c7-f656-4a1d-ace0-9410894f60a6
-- title:
--   Locality of LE
-- statement:
--   Locality of LE
--
--   If all inputs agree componentwise on an open V, then LE agrees on V.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** LE 的局部性。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Local.lean#L113-L130; SHA-256 22f1948c7ec852d0260a8d87f757e6bd46a144762f64052761edd27278c8e87a. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Local
open scoped ContDiff
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas
open ExactVacuumAtlas.Variation
variable {V : Set (Pt 4)} {g g' ginv ginv' h h' : Metric 4} {F F' f f' : TwoForm 4}

theorem ExactVacuumAtlas.Variation.linEinstein_congr (hV : IsOpen V) (hg : ∀ i j, Set.EqOn (g i j) (g' i j) V)
    (hgi : ∀ i j, Set.EqOn (ginv i j) (ginv' i j) V) (hF : ∀ i j, Set.EqOn (F i j) (F' i j) V)
    (hh : ∀ i j, Set.EqOn (h i j) (h' i j) V) (hf : ∀ i j, Set.EqOn (f i j) (f' i j) V)
    {x : Pt 4} (hx : x ∈ V) (a b : Fin 4) :
    linEinstein g ginv F h f a b x = linEinstein g' ginv' F' h' f' a b x := by sorry
