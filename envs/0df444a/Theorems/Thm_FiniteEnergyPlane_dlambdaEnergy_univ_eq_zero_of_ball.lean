-- Prove2me | Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_univ_eq_zero_of_ball
-- name    : FiniteEnergyPlane.dlambdaEnergy_univ_eq_zero_of_ball
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-26T16:40:18.731562+00:00
-- url     : https://prove2.me/theorems/f1b92aff-03d2-45ae-9829-a1cc7af9821e
-- title:
--   Vanishing dλ-energy on all discs implies vanishing dλ-energy on the plane
-- statement:
--   Let $S=H^{-1}(1)$ be a level set with the induced contact form $\lambda$, and let $w:\mathbb{C}\to\mathbb{R}^{2n+2}$ be any map. Write $E_{d\lambda}(w;A)=\int_A w^*d\lambda$ for the $d\lambda$-energy of $w$ on a set $A\subseteq\mathbb{C}$, that is, the lower Lebesgue integral of the positive part of the $d\lambda$-density. If $E_{d\lambda}(w;B_R(0))=0$ for every $R\in\mathbb{R}$, then $E_{d\lambda}(w;\mathbb{C})=0$.
--
--   This lets a statement about the $d\lambda$-energy on every disc be read as a statement about the whole plane, for example when comparing with results on finite-energy planes.
--
--   **Formalization Note** The $d\lambda$-energy is `dlambdaEnergy H A w`, the `lintegral` over `A` of `ENNReal.ofReal (dlambdaDensity H w z)`. No regularity of $w$ is assumed. For $R\le0$ the disc `ball 0 R` is empty.
-- source:
--   Standard

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- If the `dλ`-energy of `w` vanishes on every disc `ball 0 R`, then the `dλ`-energy of `w` on all
of `ℂ` vanishes. -/
theorem dlambdaEnergy_univ_eq_zero_of_ball {n : ℕ} (H : V n → ℝ) (w : ℂ → V n)
    (h0 : ∀ R : ℝ, dlambdaEnergy H (ball 0 R) w = 0) : dlambdaEnergy H Set.univ w = 0 := by
  sorry

end FiniteEnergyPlane
