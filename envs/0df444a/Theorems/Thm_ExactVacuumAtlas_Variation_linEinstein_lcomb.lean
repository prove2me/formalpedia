-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_linEinstein_lcomb
-- name    : ExactVacuumAtlas.Variation.linEinstein_lcomb
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:51:49.121688+00:00
-- url     : https://prove2.me/theorems/e2504aa2-2828-4220-8d80-7de85ad71c04
-- title:
--   Linearity of the linearised Einstein operator
-- statement:
--   Linearity of the linearised Einstein operator
--
--   For open U ⊆ ℝ⁴, C^∞ g, ginv, h₁, h₂ on U, arbitrary F, f₁, f₂, reals c₁, c₂ and x ∈ U: LE_ab(g, ginv, F; c₁h₁ + c₂h₂, c₁f₁ + c₂f₂)(x) = c₁ LE_ab(g, ginv, F; h₁, f₁)(x) + c₂ LE_ab(g, ginv, F; h₂, f₂)(x).
--
--   **Scope.** Pointwise on open U; C^∞ needed for the derivative terms of h (the f-dependence of LE is algebraic). The maxwell/faraday analogues are separate nodes.
--
--   **中文摘要** LE 对 (h,f) 的线性性（开集上 C^∞ 背景与 C^∞ 的 h₁,h₂；f₁,f₂、F 任意）。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Local.lean#L230-L237; SHA-256 22f1948c7ec852d0260a8d87f757e6bd46a144762f64052761edd27278c8e87a. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.Variation.linEinstein_lcomb (f₁ f₂ : TwoForm 4) {x : Pt 4} (hx : x ∈ U) (a b : Fin 4) :
    linEinstein g ginv F (lcomb c₁ h₁ c₂ h₂) (lcomb c₁ f₁ c₂ f₂) a b x =
      c₁ * linEinstein g ginv F h₁ f₁ a b x + c₂ * linEinstein g ginv F h₂ f₂ a b x := by sorry
