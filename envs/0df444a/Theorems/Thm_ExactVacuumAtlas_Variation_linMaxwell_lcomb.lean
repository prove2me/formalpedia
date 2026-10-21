-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_linMaxwell_lcomb
-- name    : ExactVacuumAtlas.Variation.linMaxwell_lcomb
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:51:50.657271+00:00
-- url     : https://prove2.me/theorems/2f5366c4-b4de-439e-b08f-574eb9abd384
-- title:
--   Linearity of LJ
-- statement:
--   Linearity of LJ
--
--   LJ is linear in (h, f): its value at c₁(h₁, f₁) + c₂(h₂, f₂) is c₁ times the value at (h₁, f₁) plus c₂ times the value at (h₂, f₂), pointwise on an open set with the C^∞ hypotheses printed in the statement.
--
--   **Scope.** Hypotheses exactly as printed.
--
--   **中文摘要** LJ 对 (h,f) 的线性性。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Local.lean#L252-L267; SHA-256 22f1948c7ec852d0260a8d87f757e6bd46a144762f64052761edd27278c8e87a. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Local
open scoped ContDiff
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas
open ExactVacuumAtlas.Variation
variable {U : Set (Pt 4)} {g ginv h₁ h₂ : Metric 4} {F f₁ f₂ : TwoForm 4} (c₁ c₂ : ℝ)
variable (hU : IsOpen U) (hg : ∀ i j, ContDiffOn ℝ ∞ (g i j) U) (hgi : ∀ i j, ContDiffOn ℝ ∞ (ginv i j) U)
include hU hg hgi
variable {c₁ c₂} (hh₁ : ∀ i j, ContDiffOn ℝ ∞ (h₁ i j) U) (hh₂ : ∀ i j, ContDiffOn ℝ ∞ (h₂ i j) U)
include hh₁ hh₂
variable (hF : ∀ i j, ContDiffOn ℝ ∞ (F i j) U) (hf₁ : ∀ i j, ContDiffOn ℝ ∞ (f₁ i j) U)
  (hf₂ : ∀ i j, ContDiffOn ℝ ∞ (f₂ i j) U)
include hF
omit hg
include hf₁ hf₂

theorem ExactVacuumAtlas.Variation.linMaxwell_lcomb {x : Pt 4} (hx : x ∈ U) (b : Fin 4) :
    linMaxwell g ginv F (lcomb c₁ h₁ c₂ h₂) (lcomb c₁ f₁ c₂ f₂) b x =
      c₁ * linMaxwell g ginv F h₁ f₁ b x + c₂ * linMaxwell g ginv F h₂ f₂ b x := by sorry
