-- Prove2me | Theorems.Thm_FiniteEnergyPlane_tendsto_dlambdaEnergy_punctured
-- name    : FiniteEnergyPlane.tendsto_dlambdaEnergy_punctured
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-26T16:43:15.484222+00:00
-- url     : https://prove2.me/theorems/384c236b-a473-4770-a88e-ccf67f2fe142
-- title:
--   dλ-energy of small punctured discs tends to zero
-- statement:
--   Let $S=H^{-1}(1)$ be a level set with the induced contact form $\lambda$, and let $u:\mathbb{C}\to\mathbb{R}^{2n+2}$ be any map. Write $E_{d\lambda}(u;A)=\int_A u^*d\lambda$ for the $d\lambda$-energy of $u$ on a set $A\subseteq\mathbb{C}$, that is, the lower Lebesgue integral of the positive part of the $d\lambda$-density. If the $d\lambda$-energy of $u$ on the punctured unit disc $\{0<|x|<1\}$ is finite, then
--   $$\lim_{r\to0^+}E_{d\lambda}\big(u;\{x\in\mathbb{C}:0<|x|<r\}\big)=0.$$
--
--   This is the form in which finiteness of energy near a puncture is used: the $d\lambda$-energy left in arbitrarily small punctured discs around the puncture is arbitrarily small.
--
--   **Formalization Note** The $d\lambda$-energy is `dlambdaEnergy H A u`, the `lintegral` over `A` of `ENNReal.ofReal (dlambdaDensity H u z)`. The limit is taken along `𝓝[>] 0`. No regularity of $u$ is assumed.
-- source:
--   Standard

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- If the `dλ`-energy of `u` on the punctured unit disc is finite, then the `dλ`-energy of `u` on
the punctured discs `0 < ‖x‖ < r` tends to `0` as `r → 0⁺`. -/
theorem tendsto_dlambdaEnergy_punctured {n : ℕ} (H : V n → ℝ) (u : ℂ → V n)
    (hD : dlambdaEnergy H {x : ℂ | x ≠ 0 ∧ ‖x‖ < 1} u ≠ ⊤) :
    Tendsto (fun r : ℝ => dlambdaEnergy H {x : ℂ | x ≠ 0 ∧ ‖x‖ < r} u) (𝓝[>] 0) (𝓝 0) := by
  sorry

end FiniteEnergyPlane
