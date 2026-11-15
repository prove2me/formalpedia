-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_continuousOn_closedBall_ne_zero_eq_of_hasLoopWind_zero
-- name    : FiniteEnergyPlane.exists_continuousOn_closedBall_ne_zero_eq_of_hasLoopWind_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-14T20:28:32.871418+00:00
-- url     : https://prove2.me/theorems/3ed16dd6-e9ec-4ff6-8cb6-30ef9b7cbe68
-- title:
--   A boundary loop of winding number zero extends to a nonvanishing map of the closed disc
-- statement:
--   Let $g:\mathbb C\to\mathbb C$, $p\in\mathbb C$ and $\rho>0$, and suppose the loop $t\mapsto g(p+\rho e^{2\pi it})$, $t\in[0,1]$, is a continuous nowhere-zero loop of winding number $0$. Then there is $h:\mathbb C\to\mathbb C$, continuous and nowhere zero on the closed disc $\overline B(p,\rho)$, with $h=g$ on the circle $|z-p|=\rho$.
--
--   This is the extension half of the planar degree criterion: winding number $0$ is the only obstruction to extending a nonvanishing boundary map over the disc.
--
--   Formalization Note: `HasLoopWind f k` (platform definition) says `f` is a continuous `1`-periodic nowhere-zero loop with winding number `k`; `ccwLoop ρ t = ρ e^{2π i t}`.
-- source:
--   Standard (planar topology)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open Metric

/-- Let `g : ℂ → ℂ`, `p ∈ ℂ` and `ρ > 0`, and suppose the loop `t ↦ g (p + ccwLoop ρ t)` along
the circle `‖z - p‖ = ρ` has winding number `0`. Then there is a function `h`, continuous and
nowhere zero on the closed disc `closedBall p ρ`, with `h = g` on the circle `sphere p ρ`. -/
theorem exists_continuousOn_closedBall_ne_zero_eq_of_hasLoopWind_zero (g : ℂ → ℂ) (p : ℂ)
    {ρ : ℝ} (hρ : 0 < ρ) (hw : HasLoopWind (fun t => g (p + ccwLoop ρ t)) 0) :
    ∃ h : ℂ → ℂ, ContinuousOn h (closedBall p ρ) ∧ (∀ z ∈ closedBall p ρ, h z ≠ 0) ∧
      ∀ z ∈ sphere p ρ, h z = g z := by
  sorry

end FiniteEnergyPlane
