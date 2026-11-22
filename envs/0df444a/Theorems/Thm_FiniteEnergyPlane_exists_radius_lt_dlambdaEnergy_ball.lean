-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_radius_lt_dlambdaEnergy_ball
-- name    : FiniteEnergyPlane.exists_radius_lt_dlambdaEnergy_ball
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-22T19:41:01.106817+00:00
-- url     : https://prove2.me/theorems/1b8665e2-26b7-4714-bcc8-5c928649e2cb
-- title:
--   Centred discs exhaust the dλ-energy
-- statement:
--   Let $u:\mathbb{C}\to\mathbb{R}^{2n}$ and $x\in[0,\infty]$ with $x<\int_{\mathbb{C}}u^*d\lambda$. Then there is $\rho\ge0$ with $x<\int_{\{|z|<\rho\}}u^*d\lambda$.
--
--   The $d\lambda$-energy on the whole plane is approached by its values on large centred discs. It is used to find a disc carrying a prescribed part of the energy of a finite-energy plane (Hryniewicz 2012, Lemma 7.2).
--
--   **Formalization Note** The $d\lambda$-energy is `dlambdaEnergy H s u = ∫⁻ z in s, ENNReal.ofReal (dlambdaDensity H u z)` with values in $[0,\infty]$; the disc is `ball 0 ρ`.
-- source:
--   General lemma; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Lemma 7.2

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- If `x` is less than the total `dλ`-energy of `u`, then `x` is less than the `dλ`-energy of `u`
on some disc `ball 0 ρ` with `ρ ≥ 0`. -/
theorem exists_radius_lt_dlambdaEnergy_ball {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (x : ℝ≥0∞)
    (hx : x < dlambdaEnergy H Set.univ u) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ x < dlambdaEnergy H (ball 0 ρ) u := by
  sorry

end FiniteEnergyPlane
