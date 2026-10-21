-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_linFaraday_lcomb
-- name    : ExactVacuumAtlas.Variation.linFaraday_lcomb
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:52:04.089247+00:00
-- url     : https://prove2.me/theorems/f255f699-1efb-4a6a-a8e2-5269d0fd9fb1
-- title:
--   Linearity of LH
-- statement:
--   Linearity of LH
--
--   On an open U ⊆ ℝ⁴, let f₁ and f₂ be componentwise C^∞, and let c₁,c₂ be real constants. For every x ∈ U and all a,b,c, LH(c₁f₁+c₂f₂)_abc(x) = c₁ LH(f₁)_abc(x) + c₂ LH(f₂)_abc(x). The operator linFaraday has only the field variation f as input; it has no metric-variation h argument.
--
--   **Scope.** Hypotheses exactly as printed.
--
--   **中文摘要** LH 对电磁场变分 f 线性：LH(c₁f₁+c₂f₂)=c₁LH(f₁)+c₂LH(f₂)；其实际接口不含度规变分 h。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Local.lean#L271-L279; SHA-256 22f1948c7ec852d0260a8d87f757e6bd46a144762f64052761edd27278c8e87a. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Local
open scoped ContDiff
open ExactVacuumAtlas.EinsteinMaxwell

theorem ExactVacuumAtlas.Variation.linFaraday_lcomb {U : Set (Pt 4)} (hU : IsOpen U) {f₁ f₂ : TwoForm 4}
    (hf₁ : ∀ i j, ContDiffOn ℝ ∞ (f₁ i j) U) (hf₂ : ∀ i j, ContDiffOn ℝ ∞ (f₂ i j) U) (c₁ c₂ : ℝ)
    {x : Pt 4} (hx : x ∈ U) (a b c : Fin 4) :
    linFaraday (lcomb c₁ f₁ c₂ f₂) a b c x = c₁ * linFaraday f₁ a b c x + c₂ * linFaraday f₂ a b c x := by sorry
